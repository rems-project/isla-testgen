// BSD 2-Clause License
//
// Copyright (c) 2020 Brian Campbell
// Copyright (c) 2020 Alasdair Armstrong
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::iter;
use std::ops::Range;

use crate::target::Target;

use isla_lib::concrete::BV;
use isla_lib::config::ISAConfig;
use isla_lib::error::ExecError;
use isla_lib::ir;
use isla_lib::ir::{Name, Ty, Val};
use isla_lib::log;
use isla_lib::memory;
use isla_lib::primop::smt_value;
use isla_lib::smt;
use isla_lib::smt::smtlib::Exp;
use isla_lib::smt::{Accessor, Checkpoint, Event, Model, SmtResult, Solver};
use isla_lib::zencode;

// TODO: get smt.rs to return a BV
fn bits_to_bv<B: BV>(bits: &[bool]) -> B {
    let mut bv = B::zeros(bits.len() as u32);
    for n in 0..bits.len() {
        if bits[n] {
            bv = bv.set_slice(n as u32, B::BIT_ONE);
        };
    }
    bv
}

// For now I128 values are repesented as bitvectors, because that's
// how they come out of Z3 and we don't really need to convert them to
// anything yet.
#[derive(Clone, Copy, Debug)]
pub enum GroundVal<B> {
    Bool(bool),
    Bits(B),
}

impl<B: BV> std::fmt::Display for GroundVal<B> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            GroundVal::Bool(true) => write!(f, "true"),
            GroundVal::Bool(false) => write!(f, "false"),
            GroundVal::Bits(bs) => std::fmt::Display::fmt(&bs, f),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum GVAccessor<N> {
    Field(N),
    Element(usize),
}

fn get_model_val<B: BV>(model: &mut Model<B>, val: &Val<B>) -> Result<Option<GroundVal<B>>, ExecError> {
    let exp = smt_value(val)?;
    match model.get_exp(&exp)? {
        Some(Exp::Bits64(bits, len)) => Ok(Some(GroundVal::Bits(B::new(bits, len)))),
        Some(Exp::Bits(bits)) => Ok(Some(GroundVal::Bits(bits_to_bv(&bits)))),
        Some(Exp::Bool(b)) => Ok(Some(GroundVal::Bool(b))),
        None => Ok(None),
        Some(exp) => Err(ExecError::Z3Error(format!("Bad bitvector model value {:?}", exp))),
    }
}

pub struct PrePostStates<'ir, B> {
    pub code: Vec<(Range<memory::Address>, Vec<u8>)>,
    pub pre_memory: Vec<(Range<memory::Address>, Vec<u8>)>,
    pub pre_registers: HashMap<(&'ir str, Vec<GVAccessor<&'ir str>>), GroundVal<B>>,
    pub post_memory: Vec<(Range<memory::Address>, Vec<u8>)>,
    pub post_registers: HashMap<(&'ir str, Vec<GVAccessor<&'ir str>>), GroundVal<B>>,
}

fn regacc_to_str<B: BV>(shared_state: &ir::SharedState<B>, regacc: &(Name, Vec<GVAccessor<Name>>)) -> String {
    let (reg, acc) = regacc;
    let reg_str = shared_state.symtab.to_str(*reg).to_string();
    let fields = acc.iter().map(|acc| match acc {
        GVAccessor::Field(a) => shared_state.symtab.to_str(*a).to_string(),
        GVAccessor::Element(i) => i.to_string(),
    });
    let parts: Vec<String> = iter::once(reg_str).chain(fields).collect();
    parts.join(".")
}

fn regacc_name<'ir, B>(
    shared_state: &ir::SharedState<'ir, B>,
    name: Name,
    accessor: &Vec<GVAccessor<Name>>,
) -> (&'ir str, Vec<GVAccessor<&'ir str>>) {
    (
        shared_state.symtab.to_str(name),
        accessor
            .iter()
            .map(|acc| match acc {
                GVAccessor::Field(field_name) => GVAccessor::Field(shared_state.symtab.to_str(*field_name)),
                GVAccessor::Element(i) => GVAccessor::Element(*i),
            })
            .collect(),
    )
}

fn regacc_int<B>(
    shared_state: &ir::SharedState<B>,
    (name, accessor): &(String, Vec<GVAccessor<String>>),
) -> (Name, Vec<GVAccessor<Name>>) {
    (
        shared_state.symtab.get(&zencode::encode(name)).expect("Register missing"),
        accessor
            .iter()
            .map(|acc| match acc {
                GVAccessor::Field(field_name) => {
                    GVAccessor::Field(shared_state.symtab.get(&zencode::encode(field_name)).expect("Field missing"))
                }
                GVAccessor::Element(i) => GVAccessor::Element(*i),
            })
            .collect(),
    )
}

fn batch_memory<T, F>(memory: &BTreeMap<u64, T>, content: &F) -> Vec<(Range<memory::Address>, Vec<u8>)>
where
    F: Fn(&T) -> Option<u8>,
{
    let mut m = Vec::new();

    let mut current = None;

    for (&address, raw) in memory {
        match content(raw) {
            None => (),
            Some(byte) => match current {
                None => current = Some((address..address + 1, vec![byte])),
                Some((old_range, mut bytes)) => {
                    if old_range.end == address {
                        bytes.push(byte);
                        current = Some((old_range.start..address + 1, bytes))
                    } else {
                        m.push((old_range, bytes));
                        current = Some((address..address + 1, vec![byte]))
                    }
                }
            },
        }
    }
    match current {
        None => (),
        Some(c) => m.push(c),
    }
    m
}

fn apply_accessors<B: BV>(
    shared_state: &ir::SharedState<B>,
    start_ty: &Ty<Name>,
    accessors: &Vec<Accessor>,
    start_value: &Val<B>,
) -> (Ty<Name>, Val<B>) {
    let mut ty = start_ty;
    let mut value = start_value;
    for Accessor::Field(field) in accessors {
        match ty {
            Ty::Struct(name) => {
                ty = shared_state.structs.get(&name).unwrap().get(&field).unwrap();
                match value {
                    Val::Struct(field_vals) => value = field_vals.get(&field).unwrap(),
                    _ => panic!("Bad value for struct {:?}", value),
                }
            }
            _ => panic!("Bad type for struct {:?}", ty),
        }
    }
    (ty.clone(), value.clone())
}

fn make_gv_accessors(accessors: &[Accessor]) -> Vec<GVAccessor<Name>> {
    accessors
        .iter()
        .map(|x| match x {
            Accessor::Field(n) => GVAccessor::Field(*n),
        })
        .collect()
}

fn iter_struct_types<F, T, B: BV>(
    shared_state: &ir::SharedState<B>,
    f: &mut F,
    ty: &Ty<Name>,
    accessors: &mut Vec<GVAccessor<Name>>,
    v: &Val<B>,
    r: &mut T,
) where
    F: FnMut(&Ty<Name>, &Vec<GVAccessor<Name>>, &Val<B>, &mut T),
{
    match ty {
        Ty::Struct(name) => match v {
            Val::Struct(field_vals) => {
                let fields = shared_state.structs.get(name).unwrap();
                for (field, ty) in fields {
                    accessors.push(GVAccessor::Field(*field));
                    iter_struct_types(shared_state, f, ty, accessors, field_vals.get(field).unwrap(), r);
                    accessors.pop();
                }
            }
            _ => panic!("Struct type, non-struct value {:?}", v),
        },
        Ty::FixedVector(_, element_type) => match v {
            Val::Vector(elements) => {
                for (i, element) in elements.iter().enumerate() {
                    accessors.push(GVAccessor::Element(i));
                    iter_struct_types(shared_state, f, element_type, accessors, element, r);
                    accessors.pop();
                }
            }
            _ => panic!("Vector type, non-vector value {:?}", v),
        },
        _ => f(ty, accessors, v, r),
    }
}

/// Extract pre- and post-states from the event trace and the model.
/// The first read after initialisation is recorded for the pre-state:
/// if it was concrete during the symbolic execution then it was
/// initialised separately and the harness doesn't need to do it;
/// however if it's not supported by the harness then we warn about
/// it.
pub fn interrogate_model<'ir, B: BV, T: Target>(
    _target: &T,
    _isa_config: &ISAConfig<B>,
    checkpoint: Checkpoint<B>,
    shared_state: &ir::SharedState<'ir, B>,
    register_types: &HashMap<Name, Ty<Name>>,
    symbolic_regions: &[Range<memory::Address>],
    symbolic_code_regions: &[Range<memory::Address>],
) -> Result<PrePostStates<'ir, B>, ExecError> {
    let cfg = smt::Config::new();
    cfg.set_param_value("model", "true");
    let ctx = smt::Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    match solver.check_sat() {
        SmtResult::Sat => (),
        SmtResult::Unsat => return Err(ExecError::Z3Error(String::from("Unsatisfiable at recheck"))),
        SmtResult::Unknown => return Err(ExecError::Z3Unknown),
    };

    // The events in the processor initialisation aren't relevant, so we take
    // them from the first instruction fetch.
    let read_kind_name = shared_state.symtab.get("zRead_ifetch").expect("Read_ifetch missing");
    let (read_kind_pos, read_kind_size) = shared_state.enum_members.get(&read_kind_name).unwrap();
    let read_kind_id = solver.get_enum(*read_kind_size);

    let mut model = Model::new(&solver);
    log!(log::VERBOSE, format!("Model: {:?}", model));

    let mut events = solver.trace().to_vec();
    let events: Vec<Event<B>> = events.drain(..).cloned().rev().collect();

    let harness_registers: HashSet<(Name, Vec<GVAccessor<Name>>)> =
        T::regs().iter().map(|ra| regacc_int(shared_state, ra)).collect();
    let mut initial_memory: BTreeMap<u64, u8> = BTreeMap::new();
    let mut current_memory: BTreeMap<u64, Option<u8>> = BTreeMap::new();
    let mut initial_registers: HashMap<(Name, Vec<GVAccessor<Name>>), GroundVal<B>> = HashMap::new();
    // The boolean in current_registers indicates that a register is
    // set by the harness or the test sequence, and so should be
    // reported to the user.
    let mut current_registers: HashMap<(Name, Vec<GVAccessor<Name>>), (bool, Option<GroundVal<B>>)> = HashMap::new();
    let mut skipped_register_reads: HashSet<(Name, Vec<GVAccessor<Name>>)> = HashSet::new();

    let mut init_complete = false;

    let is_ifetch = |val: &Val<B>| match val {
        Val::Enum(ir::EnumMember { enum_id, member }) => *enum_id == read_kind_id && *member == *read_kind_pos,
        _ => false,
    };

    for event in events {
        match &event {
            Event::ReadMem { value, read_kind, address, bytes } if init_complete || is_ifetch(read_kind) => {
                if !init_complete {
                    init_complete = true;
                    // We explicitly reset these registers to symbolic variables after
                    // symbolic execution of the model initialisation, so throw away
                    // any current value, especially as we want to find out if we need
                    // to set them in the actual test and so should not ignore the next
                    // write.
                    for regacc in &harness_registers {
                        current_registers.remove(regacc);
                    }
                }
                let address = match get_model_val(&mut model, address)? {
                    Some(GroundVal::Bits(bs)) => bs,
                    Some(GroundVal::Bool(_)) => panic!("Memory read address was a boolean?!"),
                    None => panic!("Arbitrary memory read address"),
                };
                let val = get_model_val(&mut model, value)?;
                match val {
                    Some(GroundVal::Bits(val)) => {
                        let vals = val.to_le_bytes();
                        if 8 * *bytes == val.len() {
                            for i in 0..*bytes {
                                let byte_address = address.try_into()? + i as u64;
                                let byte_val = vals[i as usize];
                                if current_memory.insert(byte_address, Some(byte_val)).is_none() {
                                    initial_memory.insert(byte_address, byte_val);
                                }
                            }
                        } else {
                            return Err(ExecError::Type("Memory read had wrong number of bytes"));
                        }
                    }
                    Some(GroundVal::Bool(_)) => panic!("Memory read returned a boolean?!"),
                    None => println!("Ambivalent read of {} bytes from {:x}", bytes, address),
                }
            }
            Event::WriteMem { value: _, write_kind: _, address, data, bytes } => {
                let address = match get_model_val(&mut model, address)? {
                    Some(GroundVal::Bits(bs)) => bs,
                    Some(GroundVal::Bool(_)) => panic!("Memory write address was a boolean?!"),
                    None => panic!("Arbitrary memory write address"),
                };
                let val = get_model_val(&mut model, data)?;
                match val {
                    Some(GroundVal::Bits(val)) => {
                        let vals = val.to_le_bytes();
                        for i in 0..*bytes {
                            current_memory.insert(address.try_into()? + i as u64, Some(vals[i as usize]));
                        }
                    }
                    Some(GroundVal::Bool(_)) => panic!("Memory write value was a boolean?!"),
                    None => {
                        println!("Ambivalent write of {} bytes to {:x}", bytes, address);
                        for i in 0..*bytes {
                            current_memory.insert(address.try_into()? + i as u64, None);
                        }
                    }
                }
            }
            Event::ReadReg(reg, accessors, value) => {
                let mut process_read_bits =
                    |ty: &Ty<Name>, accessors: &Vec<GVAccessor<Name>>, value: &Val<B>, skipped: &mut HashSet<_>| {
                        let key = (*reg, accessors.clone());
                        if skipped.contains(&key) {
                            return;
                        };
                        if init_complete {
                            match ty {
                                Ty::Bits(_) | Ty::Bool | Ty::I128 => {
                                    let model_value = get_model_val(&mut model, value).expect("get_model_val");
                                    match value {
                                        Val::Symbolic(_) => {
                                            if current_registers.insert(key.clone(), (true, model_value)).is_none() {
                                                match model_value {
                                                    Some(val) => {
                                                        initial_registers.insert(key, val);
                                                    }
                                                    None => println!(
                                                        "Ambivalent read of register {}",
                                                        regacc_to_str(shared_state, &key)
                                                    ),
                                                }
                                            }
                                        }
                                        // Otherwise we read a concrete initial value, so it comes from
                                        // initialisation and does not need to be set by the harness
                                        _ => {
                                            current_registers.insert(key.clone(), (false, model_value));
                                        }
                                    }
                                }
                                _ => {
                                    println!(
                                        "Skipping read of {} with value {:?} due to unsupported type {:?}",
                                        regacc_to_str(shared_state, &key),
                                        value,
                                        ty
                                    );
                                    skipped.insert(key);
                                }
                            }
                        }
                    };
                match register_types.get(reg) {
                    Some(ty) => {
                        let (read_ty, read_value) = apply_accessors(shared_state, ty, accessors, &value);
                        iter_struct_types(
                            shared_state,
                            &mut process_read_bits,
                            &read_ty,
                            &mut make_gv_accessors(accessors),
                            &read_value,
                            &mut skipped_register_reads,
                        )
                    }
                    None => panic!("Missing type for register {}", shared_state.symtab.to_str(*reg)),
                }
            }
            Event::WriteReg(reg, accessors, value) => {
                let mut process_write =
                    |ty: &Ty<Name>, accessors: &Vec<GVAccessor<Name>>, value: &Val<B>, _: &mut ()| {
                        let key = (*reg, accessors.clone());
                        match ty {
                            Ty::Bits(_) | Ty::Bool => {
                                let val = get_model_val(&mut model, value).expect("get_model_val");
                                current_registers.insert(key, (init_complete, val));
                            }
                            _ => (),
                        }
                    };
                match register_types.get(reg) {
                    Some(ty) => {
                        let (assigned_ty, assigned_value) = apply_accessors(shared_state, ty, accessors, &value);
                        iter_struct_types(
                            shared_state,
                            &mut process_write,
                            &assigned_ty,
                            &mut make_gv_accessors(accessors),
                            &assigned_value,
                            &mut (),
                        )
                    }
                    None => panic!("Missing type for register {}", shared_state.symtab.to_str(*reg)),
                }
            }
            Event::Instr(_) if !init_complete => {
                // We should see the instruction fetch first and look
                // at events from then on
                panic!("Instruction announced without an ifetch");
            }
            _ => (),
        }
    }

    println!("Initial memory:");
    for (address, value) in &initial_memory {
        print!("{:08x}:{:02x} ", address, value);
    }
    println!();
    for (regacc, _value) in &initial_registers {
        if !harness_registers.contains(regacc) {
            println!("Warning: depends on unsupported register {}", regacc_to_str(shared_state, regacc));
        }
    }
    print!("Initial registers: ");
    for (regacc, value) in &initial_registers {
        print!("{}:{} ", regacc_to_str(shared_state, regacc), value);
    }
    println!();

    println!("Final memory:");
    for (address, value) in &current_memory {
        match value {
            Some(val) => print!("{:08x}:{:02x} ", address, val),
            None => print!("{:08x}:?? ", address),
        }
    }
    println!();
    print!("Final registers: ");
    for (regacc, (post_init, value)) in &current_registers {
        if *post_init {
            match value {
                Some(val) => print!("{}:{} ", regacc_to_str(shared_state, regacc), val),
                None => print!("{}:?? ", regacc_to_str(shared_state, regacc)),
            }
        }
    }
    println!();

    let mut initial_symbolic_memory: Vec<(Range<memory::Address>, Vec<u8>)> =
        symbolic_regions.iter().map(|r| (r.clone(), vec![0; (r.end - r.start) as usize])).collect();

    let mut initial_symbolic_code_memory: Vec<(Range<memory::Address>, Vec<u8>)> =
        symbolic_code_regions.iter().map(|r| (r.clone(), vec![0; (r.end - r.start) as usize])).collect();

    for (address, value) in &initial_memory {
        for (r, v) in &mut initial_symbolic_memory {
            if r.contains(address) {
                v[(address - r.start) as usize] = *value;
                break;
            }
        }
        for (r, v) in &mut initial_symbolic_code_memory {
            if r.contains(address) {
                v[(address - r.start) as usize] = *value;
                break;
            }
        }
    }

    let pre_registers =
        initial_registers.iter().map(|((reg, acc), gv)| (regacc_name(shared_state, *reg, acc), *gv)).collect();
    let post_registers = current_registers
        .iter()
        .filter_map(|((reg, acc), (_, optional_gv))| match optional_gv {
            Some(gv) => Some((regacc_name(shared_state, *reg, acc), *gv)),
            None => None,
        })
        .collect();
    let post_memory = batch_memory(&current_memory, &(|x: &Option<u8>| *x));

    Ok(PrePostStates {
        pre_memory: initial_symbolic_memory,
        code: initial_symbolic_code_memory,
        pre_registers,
        post_registers,
        post_memory,
    })
}
