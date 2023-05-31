use std::collections::{HashMap, HashSet};

use isla_lib::bitvector::BV;
use isla_lib::ir::{BitsSegment, Val};
use isla_lib::log;
use isla_lib::smt::{Event, Sym};
use isla_lib::smt::smtlib::{Def, Exp, Ty};

// Check that a trace doesn't depend on the solver choosing particular
// values for undefined bits.

// This is currently limited to checking values written to memory or
// used for control flow.  We can't tell the difference in the
// (current) traces between assertions that are intended to limit the
// range of an undefined value and those which check an internal
// property.  As a result the checker won't pick up a dependency for
// one of these assertions.

// The mapping of SMT varables to undefined bits is returned so that
// we can give masks for checking registers in the output.

fn check_value<B: BV>(
    v: &Val<B>,
    var_undefs: &HashMap<Sym, B>,
) -> bool {
    use Val::*;

    let check_var = |var| var_undefs.get(var).map(|b| b.is_zero()).unwrap_or(true);
    match v {
        Symbolic(var) => check_var(var),
        I64(_) | I128(_) | Bool(_) | Bits(_) | String(_) | Unit | Enum(_) | Poison => true,
        MixedBits(segments) => segments.iter().all(|seg| match seg {
            BitsSegment::Symbolic(var) => check_var(var),
            BitsSegment::Concrete(_) => true,
        }),
        Vector(vals) | List(vals) => vals.iter().all(|val| check_value(val, var_undefs)),
        Struct(vals) => vals.values().all(|val| check_value(val, var_undefs)),
        Ctor(_, val) => check_value(val, var_undefs),
        SymbolicCtor(var, vals) => check_var(var) && vals.values().all(|val| check_value(val, var_undefs)),
        Ref(_) => panic!("Unsupported ref value"),
    }
}

fn examine_exp<B: BV>(
    exp: &Exp<Sym>,
    var_undefs: &HashMap<Sym, B>,
) -> Result<Option<B>, String> {
    use Exp::*;

    let undef =
        match exp {
            Var(v) => var_undefs.get(v).map(|b| b.clone()),
            Bits(_) | Bits64(_) | Enum(_) | Bool(_) => None,
            // We treat booleans as single bits
            Eq(e1, e2) | Neq(e1, e2) | And(e1, e2) | Or(e1, e2) => {
                match (examine_exp(e1, var_undefs)?, examine_exp(e2, var_undefs)?) {
                    (None, None) => None,
                    (Some(m), None) | (None, Some(m)) => {
                        if m.is_zero() {
                            None
                        } else {
                            Some(B::ones(1))
                        }
                    }
                    (Some(m1), Some(m2)) => {
                        if m1.is_zero() & m2.is_zero() {
                            None
                        } else {
                            Some(B::ones(1))
                        }
                    }
                }
            }
            Not(e) => {
                if let Some(m) = examine_exp(e, var_undefs)? {
                    if m.is_zero() {
                        None
                    } else {
                        Some(B::ones(1))
                    }
                } else {
                    None
                }
            }
            Bvnot(e) => examine_exp(e, var_undefs)?,
            // Bitwise operations with potential for removing
            // undefined bits.  We sometimes need to do a little
            // evaluation to get a concrete value for clearing/setting
            // bits.
            Bvand(e1, e2) => {
                match (e1.clone().eval(), e2.clone().eval()) {
                    (Bits64(bs), e) | (e, Bits64(bs)) => {
                        if let Some(undef) = examine_exp(&e, var_undefs)? {
                            Some(undef & B::from_u64(bs.lower_u64()))
                        } else {
                            None
                        }
                    }
                    _ => {
                        if let Some(v1) = examine_exp(e1, var_undefs)? {
                            if let Some(v2) = examine_exp(e2, var_undefs)? {
                                Some(v1 | v2)
                            } else {
                                Some(v1)
                            }
                        } else if let Some(v2) = examine_exp(e2, var_undefs)? {
                            Some(v2)
                        } else {
                            None
                        }
                    }
                }
            }
            Bvor(e1, e2) => {
                match (e1.clone().eval(), e2.clone().eval()) {
                    (Bits64(bs), e) | (e, Bits64(bs)) => {
                        if let Some(undef) = examine_exp(&e, var_undefs)? {
                            Some(undef & !B::from_u64(bs.lower_u64()))
                        } else {
                            None
                        }
                    }
                    _ => {
                        if let Some(v1) = examine_exp(e1, var_undefs)? {
                            if let Some(v2) = examine_exp(e2, var_undefs)? {
                                Some(v1 | v2)
                            } else {
                                Some(v1)
                            }
                        } else if let Some(v2) = examine_exp(e2, var_undefs)? {
                            Some(v2)
                        } else {
                            None
                        }
                    }
                }
            }
            // Other bitwise operations
            Bvxor(e1, e2) | Bvnand(e1, e2) | Bvnor(e1, e2) | Bvxnor(e1, e2) => {
                if let Some(v1) = examine_exp(e1, var_undefs)? {
                    if let Some(v2) = examine_exp(e2, var_undefs)? {
                        Some(v1 | v2)
                    } else {
                        Some(v1)
                    }
                } else if let Some(v2) = examine_exp(e2, var_undefs)? {
                    Some(v2)
                } else {
                    None
                }
            }
            // For these, return all potentially undefined if any arguments bits are.
            Bvneg(e) => {
                if let Some(undef) = examine_exp(e, var_undefs)? {
                    if undef.is_zero() { None } else { Some(B::ones(undef.len())) }
                } else {
                    None
                }
            }
            Bvadd(e1, e2) | Bvsub(e1, e2) | Bvmul(e1, e2) | Bvudiv(e1, e2) | Bvsdiv(e1, e2)
                | Bvurem(e1, e2) | Bvsrem(e1, e2) | Bvsmod(e1, e2) => {
                    match (examine_exp(e1, var_undefs)?, examine_exp(e2, var_undefs)?) {
                        (None, None) => None,
                        (Some(undef), None) | (None, Some(undef)) => {
                            if undef.is_zero() { None } else { Some(B::ones(undef.len())) }
                        }
                        (Some(m1), Some(m2)) => {
                            if m1.is_zero() & m2.is_zero() { None } else { Some(B::ones(m1.len())) }
                        }
                    }
                }
            // Comparisons
            Bvult(e1, e2) | Bvslt(e1, e2) | Bvule(e1, e2) | Bvsle(e1, e2) | Bvuge(e1, e2) | Bvsge(e1, e2)
                | Bvugt(e1, e2) | Bvsgt(e1, e2) => {
                    match (examine_exp(e1, var_undefs)?, examine_exp(e2, var_undefs)?) {
                        (None, None) => None,
                        (Some(undef), None) | (None, Some(undef)) => {
                            if undef.is_zero() { None } else { return Err("Comparison on undefined bits".to_string()) }
                        }
                        (Some(m1), Some(m2)) => {
                            if m1.is_zero() & m2.is_zero() { None } else { return Err("Comparison on undefined bits".to_string()) }
                        }
                    }
                }
            Extract(hi, lo, e) => {
                if let Some(undef) = examine_exp(e, var_undefs)? {
                    let len = hi - lo + 1;
                    if let Some(new_undef) = undef.slice(*lo, len) {
                        Some(new_undef)
                    } else {
                        return Err(format!("Failed on Extract({}, {}, {:?} : {})", hi, lo, e, undef.len()))
                    }
                } else {
                    None
                }
            }
            ZeroExtend(extra, e) => {
                if let Some(undef) = examine_exp(e, var_undefs)? {
                    Some(undef.zero_extend(undef.len() + *extra))
                } else {
                    None
                }
            }
            SignExtend(extra, e) => {
                if let Some(undef) = examine_exp(e, var_undefs)? {
                    // If the sign bit is undefined, the new ones will be
                    Some(undef.sign_extend(undef.len() + *extra))
                } else {
                    None
                }
            }
            Bvshl(e1, e2) => {
                if let Bits64(bs) = e2.as_ref() {
                    if let Some(lhs) = examine_exp(e1, var_undefs)? {
                        Some(lhs.shl(B::from_u64(bs.lower_u64())))
                    } else {
                        None
                    }
                } else {
                    match (examine_exp(e1, var_undefs)?, examine_exp(e2, var_undefs)?) {
                        (None, None) => None,
                        (None, Some(rhs)) => if rhs.is_zero() { None } else { return Err("Shift by undefined amount".to_string()); },
                        (Some(lhs), _) => Some(B::ones(lhs.len())),
                    }
                }
            }
            Bvlshr(e1, e2) => {
                if let Bits64(bs) = e2.as_ref() {
                    if let Some(lhs) = examine_exp(e1, var_undefs)? {
                        Some(lhs.shr(B::from_u64(bs.lower_u64())))
                    } else {
                        None
                    }
                } else {
                    match (examine_exp(e1, var_undefs)?, examine_exp(e2, var_undefs)?) {
                        (None, None) => None,
                        (None, Some(rhs)) => if rhs.is_zero() { None } else { return Err("Shift by undefined amount".to_string()); },
                        (Some(lhs), _) => Some(B::ones(lhs.len())),
                    }
                }
            }
            Bvashr(e1, e2) => {
                if let Bits64(_bs) = e2.as_ref() {
                    if let Some(lhs) = examine_exp(e1, var_undefs)? {
                        // There isn't a built-in operator for this, not worth implementing
                        Some(B::ones(lhs.len()))
                    } else {
                        None
                    }
                } else {
                    match (examine_exp(e1, var_undefs)?, examine_exp(e2, var_undefs)?) {
                        (None, None) => None,
                        (None, Some(rhs)) => if rhs.is_zero() { None } else { return Err("Shift by undefined amount".to_string()); },
                        (Some(lhs), _) => Some(B::ones(lhs.len())),
                    }
                }
            }
            Concat(e1, e2) => {
                match (examine_exp(e1, var_undefs)?, examine_exp(e2, var_undefs)?) {
                    (None, None) => None,
                    (Some(m1), Some(m2)) => Some(m1.append(m2).ok_or("concat too long".to_string())?),
                    (None, Some(m)) | (Some(m), None) => {
                        if m.is_zero() {
                            None
                        } else {
                            return Err("Concat partly defined on to unknown size".to_string()); // TODO: probably can't stand for this
                        }
                    }
                }
            }
            Ite(e1, e2, e3) => {
                if let Some(m) = examine_exp(e1, var_undefs)? {
                    if !m.is_zero() {
                        return Err("If-then-else depends on potentially undef value".to_string());
                    }
                };
                match (examine_exp(e2, var_undefs)?, examine_exp(e3, var_undefs)?) {
                    (None, r) | (r, None) => r,
                    (Some(m2), Some(m3)) => Some(m2 | m3),
                }
            }
            App(var, args) => {
                if let Some(m) = var_undefs.get(var) {
                    if !m.is_zero() {
                        return Err("App on pot undef".to_string());
                    }
                }
                for arg in args {
                    if let Some(m) = examine_exp(arg, var_undefs)? {
                        if !m.is_zero() {
                            return Err("App arg on pot undef".to_string());
                        }
                    }
                }
                None
            }
            Select(e1, e2) => {
                for exp in [e1, e2] {
                    if let Some(m) = examine_exp(exp, var_undefs)? {
                        if !m.is_zero() {
                            return Err("Select on pot undef".to_string());
                        }
                    }
                }
                None
            }
            Store(e1, e2, e3) => {
                for exp in [e1, e2, e3] {
                    if let Some(m) = examine_exp(exp, var_undefs)? {
                        if !m.is_zero() {
                            return Err("Store on pot undef".to_string());
                        }
                    }
                }
                None
            }
            Distinct(es) => {
                for exp in es {
                    if let Some(m) = examine_exp(exp, var_undefs)? {
                        if !m.is_zero() {
                            return Err("Distinct on pot undef".to_string());
                        }
                    }
                }
                None
            }
            FPConstant(_, _, _) => None,
            FPRoundingMode(_) => None,
            FPUnary(_, e) => {
                if let Some(m) = examine_exp(e, var_undefs)? {
                    if !m.is_zero() {
                        return Err("FPUnary on potentially undefined bits".to_string());
                    }
                }
                None
            }
            FPRoundingUnary(_, e1, e2) => {
                for exp in [e1, e2] {
                    if let Some(m) = examine_exp(exp, var_undefs)? {
                        if !m.is_zero() {
                            return Err("FPRoundingUnary on pot undef".to_string());
                        }
                    }
                }
                None
            }
            FPBinary(_, e1, e2) =>  {
                for exp in [e1, e2] {
                    if let Some(m) = examine_exp(exp, var_undefs)? {
                        if !m.is_zero() {
                            return Err("FPBinary on pot undef".to_string());
                        }
                    }
                }
                None
            }
            FPRoundingBinary(_, e1, e2, e3) =>  {
                for exp in [e1, e2, e3] {
                    if let Some(m) = examine_exp(exp, var_undefs)? {
                        if !m.is_zero() {
                            return Err("FPRoundingBinary on pot undef".to_string());
                        }
                    }
                }
                None
            }
            FPfma(e1, e2, e3, e4) =>  {
                for exp in [e1, e2, e3, e4] {
                    if let Some(m) = examine_exp(exp, var_undefs)? {
                        if !m.is_zero() {
                            return Err("FPfma on pot undef".to_string());
                        }
                    }
                }
                None
            }
        };
    Ok(undef)
}

fn check_smt<B: BV>(
    def: &Def,
    var_undefs: &mut HashMap<Sym, B>,
) -> Result<(), String> {
    use Def::*;
    
    match def {
        DeclareConst(var, ty) => {
            if let Ty::BitVec(size) = ty {
                log!(log::VERBOSE, format!("{} is a bitvector of size {}", var, size));
                var_undefs.insert(*var, B::ones(*size));
            }
        }
        DeclareFun(_, _, _) => (),
        DefineConst(var, exp) => {
            if let Some(undef) = examine_exp(exp, var_undefs)? {
                log!(log::VERBOSE, format!("Var {} is {}", var, undef));
                var_undefs.insert(*var, undef);
            } else {
                log!(log::VERBOSE, format!("Var {} is defined", var));
            }
        }
        DefineEnum(_) => (),
        Assert(Exp::Eq(lhs, rhs)) if matches!(lhs.as_ref(), Exp::Var(_)) & matches!(rhs.as_ref(), Exp::Bits(_) | Exp::Bits64(_)) => {
            match lhs.as_ref() {
                Exp::Var(v) => {
                    log!(log::VERBOSE, format!("Clearing {}", v));
                    var_undefs.remove(v);
                }
                _ => panic!("var not a var?!"),
            }
        }
        // See the discussion at the top
        Assert(_exp) => (),
    }
    Ok(())
}

fn clear_unwritten<B: BV>(var_undefs: &mut HashMap<Sym, B>, v: &Val<B>, written: &HashSet<Sym>) {
    use Val::*;

    match v {
        Symbolic(var) => if !written.contains(var) { log!(log::VERBOSE, format!("Clearing {}", var)); var_undefs.remove(var); },
        I64(_) | I128(_) | Bool(_) | Bits(_) | String(_) | Unit | Enum(_) | Poison => (),
        MixedBits(segments) => {
            for segment in segments {
                match segment {
                    BitsSegment::Symbolic(var) => if !written.contains(var) { log!(log::VERBOSE, format!("Clearing {}", var)); var_undefs.remove(var); },
                    BitsSegment::Concrete(_) => (),
                }
            }
        }
        Vector(vals) | List(vals) => for val in vals { clear_unwritten(var_undefs, val, written) },
        Struct(vals) => for val in vals.values() { clear_unwritten(var_undefs, val, written) },
        Ctor(_, val) => clear_unwritten(var_undefs, val, written),
        SymbolicCtor(var, vals) => {
            if !written.contains(var) { var_undefs.remove(var); };
            for val in vals.values() { clear_unwritten(var_undefs, val, written) }
        }
        Ref(_) => panic!("Unsupported ref value"),
    }
}

fn note_written<B: BV>(written: &mut HashSet<Sym>, v: &Val<B>) {
    use Val::*;

    match v {
        Symbolic(var) => { written.insert(*var); }
        I64(_) | I128(_) | Bool(_) | Bits(_) | String(_) | Unit | Enum(_) | Poison => (),
        MixedBits(segments) => {
            for segment in segments {
                match segment {
                    BitsSegment::Symbolic(var) => { written.insert(*var); }
                    BitsSegment::Concrete(_) => (),
                }
            }
        }
        Vector(vals) | List(vals) => for val in vals { note_written(written, val) },
        Struct(vals) => for val in vals.values() { note_written(written, val) },
        Ctor(_, val) => note_written(written, val),
        SymbolicCtor(var, vals) => {
            written.insert(*var);
            for val in vals.values() { note_written(written, val) }
        }
        Ref(_) => panic!("Unsupported ref value"),
    }
}

pub fn check_undefined_bits<'a, B: BV, I: Iterator<Item = &'a Event<B>>>(
    events: I,
    files: &[&str],
) -> Result<HashMap<Sym, B>, String> {
    use Event::*;

    let mut var_undefs: HashMap<Sym, B> = HashMap::new();
    let mut written: HashSet<Sym> = HashSet::new();

    for event in events {
        match event {
            Smt(def, _, _) => check_smt(&def, &mut var_undefs)?,
            Fork(_, assertion, _, loc) => {
                log!(log::VERBOSE, format!("Fork at {} depends on {}", loc.location_string(files), assertion));
                if !var_undefs.get(assertion).map(|b| b.is_zero()).unwrap_or(true) {
                    return Err(format!("Fork depends on undefined bits at {}", loc.location_string(files)));
                }
            }
            Function { .. } => (),
            Abstract { .. } | AssumeFun { .. } | UseFunAssumption { .. } => panic!("Unsupported event: {:?}", event),
            AssumeReg(_, _, _) | MarkReg { .. } | Branch { .. } | Cycle | Instr(_) | Assume(_) => (),
            ReadReg(_, _, val) => clear_unwritten(&mut var_undefs, val, &written),
            WriteReg(_, _, val) => note_written(&mut written, val),
            ReadMem {value, read_kind, address, bytes: _, tag_value: _, opts: _, region: _} => {
                if !check_value(read_kind, &var_undefs) {
                    return Err("Undefined bits used in read kind".to_string());
                }
                if !check_value(address, &var_undefs) {
                    return Err("Undefined bits used in read address".to_string());
                }
                clear_unwritten(&mut var_undefs, value, &written);
            }
            WriteMem {value, write_kind, address, data, bytes: _, tag_value, opts: _, region: _} => {
                if !var_undefs.get(value).map(|b| b.is_zero()).unwrap_or(true) {
                    return Err("Undefined bits written to memory".to_string());
                };
                if !check_value(write_kind, &var_undefs) {
                    return Err("Undefined bits used in write_kind".to_string());
                }
                if !check_value(address, &var_undefs) {
                    return Err("Undefined bits used in write address".to_string());
                }
                if !check_value(data, &var_undefs) {
                    return Err("Undefined bits used in write data".to_string());
                }
                if !tag_value.as_ref().map(|v| check_value(v, &var_undefs)).unwrap_or(true) {
                    return Err("Undefined bits used in write tag".to_string());
                }
            }
        }
    }
    Ok(var_undefs)
}

#[cfg(test)]
mod tests {
    use isla_lib::bitvector::BV;
    use isla_lib::bitvector::b64::B64;
    use isla_lib::ir::Val;
    use isla_lib::source_loc::SourceLoc;
    use isla_lib::smt::{DefAttrs, Event::*, Sym, WriteOpts};
    use isla_lib::smt::smtlib::Ty::*;
    use isla_lib::smt::smtlib::Def::*;
    use super::check_undefined_bits;
    
    #[test]
    fn simple_undef() {
        let attrs = DefAttrs::default();
        let loc = SourceLoc::unknown();
        let data = Sym::from_u32(0);
        let value = Sym::from_u32(1);
        let opts = WriteOpts::default();
        let events = vec![
            Smt(DeclareConst(data, BitVec(32)), attrs, loc),
            Smt(DeclareConst(value, Bool), attrs, loc),
            WriteMem { value, write_kind: Val::Unit, address: Val::Bits(B64::from_u64(0x1234)), data: Val::Symbolic(data), bytes: 4, tag_value: None, opts, region: "" },
        ];
            
        assert!(check_undefined_bits(events.iter(), &[]).is_err());
    }
}
