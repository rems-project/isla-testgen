use std::collections::HashMap;
use std::ops::Range;

use isla_lib::concrete::BV;
use isla_lib::executor::LocalFrame;
use isla_lib::ir::{SharedState};
use isla_lib::smt::{smtlib, Solver, Sym};
use isla_lib::zencode;

use crate::extract_state::GVAccessor;

// For now we only need one entry in the translation table (and only
// for Morello), so this is (address range, entry address, entry data).
pub type TranslationTableInfo = (Range<u64>, u64, u64);

pub trait Target
where
    Self: Sync,
{
    /// Registers supported by the test harness
    fn regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)>;
    /// Any additional initialisation
    fn init<'ir, B: BV>(
        &self,
        shared_state: &SharedState<'ir, B>,
        frame: &mut LocalFrame<B>,
        solver: &mut Solver<B>,
        init_pc: u64,
        regs: HashMap<String, Sym>,
    );
    fn translation_table_info(&self) -> Option<TranslationTableInfo>;
    fn is_gpr(name: &str) -> Option<u32>;
    fn gpr_prefix() -> &'static str;
    fn gpr_pad() -> bool;
    fn postprocess<'ir, B: BV>(&self,
        shared_state: &SharedState<'ir, B>,
        frame: &LocalFrame<B>,
        solver: &mut Solver<B>,
    ) -> Result<(), String>;
    // I'd like to move the stuff below to the config
    fn run_instruction_function() -> String;
    fn has_capabilities(&self) -> bool;
    fn run_in_el0(&self) -> bool;
    fn final_instruction(&self, exit_register: u32) -> u32;
}

pub struct Aarch64 {}

impl Target for Aarch64 {
    fn regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)> {
        let mut regs: Vec<(String, Vec<GVAccessor<String>>)> = (0..31).map(|r| (format!("R{}", r), vec![])).collect();
        let mut other_regs = ["SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3"].iter().map(|r| (r.to_string(), vec![])).collect();
        let mut flags = ["N", "Z", "C", "V"]
            .iter()
            .map(|flag| ("PSTATE".to_string(), vec![GVAccessor::Field(flag.to_string())]))
            .collect();
        regs.append(&mut other_regs);
        regs.append(&mut flags);
        regs
    }
    fn init<'ir, B: BV>(
        &self,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<B>,
        _solver: &mut Solver<B>,
        _init_pc: u64,
        _regs: HashMap<String, Sym>,
    ) {
    }
    fn translation_table_info(&self) -> Option<TranslationTableInfo> {
        None
    }
    fn is_gpr(name: &str) -> Option<u32> {
        if name.starts_with("zR") {
            let reg_str = &name[2..];
            u32::from_str_radix(reg_str, 10).ok()
        } else {
            None
        }
    }
    fn gpr_prefix() -> &'static str {
        "zR"
    }
    fn gpr_pad() -> bool {
        false
    }
    fn run_instruction_function() -> String {
        "Step_CPU".to_string()
    }
    fn postprocess<'ir, B: BV>(&self,
        _shared_state: &SharedState<'ir, B>,
        _frame: &LocalFrame<B>,
        _solver: &mut Solver<B>,
    ) -> Result<(), String> {
        Ok(())
    }
    fn has_capabilities(&self) -> bool {
        false
    }
    fn run_in_el0(&self) -> bool {
	false
    }
    fn final_instruction(&self, exit_register: u32) -> u32 {
        0xd61f0000 | (exit_register << 5) // br exit_register
    }
}

#[derive(Clone,Copy)]
pub enum MorelloStyle { AArch64Compatible, EL3Only, EL0 }

pub struct Morello {
    pub style: MorelloStyle,
    pub translation_in_symbolic_execution: bool,
}

pub fn translation_table_exp(tt_info: &TranslationTableInfo, read_exp: smtlib::Exp, addr_exp: smtlib::Exp, bytes: u32) -> smtlib::Exp {
    let (addresses, tt_base, entry) = tt_info;
    let tt_base = *tt_base;
    let entry = *entry;
    use smtlib::Exp::{And, Ite, Eq, Bits64, Bvule, Bvult};

    let bits = 8 * bytes;
    let mask: u64 = 0xffffffffffffffff >> 64 - bits;
    let address_prop = And(Box::new(Bvule(Box::new(Bits64(addresses.start, 64)), Box::new(addr_exp.clone()))),
                           Box::new(Bvult(Box::new(addr_exp.clone()), Box::new(Bits64(addresses.end, 64)))));
    let value_exp =
        Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(Bits64(tt_base, 64)))),
            Box::new(Bits64(entry & mask, bits)),
            Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(Bits64(tt_base + 1, 64)))),
                         Box::new(Bits64((entry >> 8) & mask, bits)),
                         Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(Bits64(tt_base + 2, 64)))),
                                      Box::new(Bits64((entry >> 16) & mask, bits)),
                                      Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(Bits64(tt_base + 3, 64)))),
                                                   Box::new(Bits64((entry >> 24) & mask, bits)),
                                                   Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(Bits64(tt_base + 4, 64)))),
                                                                Box::new(Bits64((entry >> 32) & mask, bits)),
                                                                Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(Bits64(tt_base + 5, 64)))),
                                                                             Box::new(Bits64((entry >> 40) & mask, bits)),
                                                                             Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(Bits64(tt_base + 6, 64)))),
                                                                                          Box::new(Bits64((entry >> 48) & mask, bits)),
                                                                                          Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(Bits64(tt_base + 7, 64)))),
                                                                                                       Box::new(Bits64((entry >> 56) & mask, bits)),
                                                                                                       Box::new(Bits64(0, bits)))))))))))))))));
    And(Box::new(address_prop),
        Box::new(Eq(Box::new(read_exp), Box::new(value_exp))))
}

impl Morello {
    fn aarch64_compatible(&self) -> bool {
       match self.style {
       MorelloStyle::AArch64Compatible => true,
       _ => false,
       }
    }
}

impl Target for Morello {
    fn regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)> {
        let mut regs: Vec<(String, Vec<GVAccessor<String>>)> =
            (0..31).map(|r| (format!("_R{:02}", r), vec![])).collect();
        let mut vector_regs = (0..32).map(|i| ("_V".to_string(), vec![GVAccessor::Element(i)])).collect();
        let mut other_regs =
            ["_PC", "SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3"].iter().map(|r| (r.to_string(), vec![])).collect();
        let mut flags = ["N", "Z", "C", "V"]
            .iter()
            .map(|flag| ("PSTATE".to_string(), vec![GVAccessor::Field(flag.to_string())]))
            .collect();
        let mut sys_regs: Vec<(String, Vec<GVAccessor<String>>)> =
            ["CPTR_EL3", "SCTLR_EL3"].iter().map(|r| (r.to_string(), vec![])).collect();
        if !self.aarch64_compatible() {
            sys_regs.push(("CCTLR_EL3".to_string(), vec![]));
            sys_regs.push(("PSTATE".to_string(), vec![GVAccessor::Field("C64".to_string())]));
            sys_regs.push(("PCC".to_string(), vec![]));
            sys_regs.push(("DDC_EL3".to_string(), vec![]));
            sys_regs.push(("RDDC_EL0".to_string(), vec![]));
            sys_regs.push(("RSP_EL0".to_string(), vec![]));
        }
	if self.run_in_el0() {
	    sys_regs.push(("PSTATE".to_string(), vec![GVAccessor::Field("EL".to_string())]));
	    sys_regs.push(("SCTLR_EL1".to_string(), vec![]));
	    sys_regs.push(("CPACR_EL1".to_string(), vec![]));
            sys_regs.push(("CCTLR_EL1".to_string(), vec![]));
            sys_regs.push(("CCTLR_EL0".to_string(), vec![]));
            sys_regs.push(("DDC_EL0".to_string(), vec![]));
	}
        regs.append(&mut vector_regs);
        regs.append(&mut other_regs);
        regs.append(&mut flags);
        regs.append(&mut sys_regs);
        regs
    }
    // TODO: aarch64_compat version of translation table
    fn translation_table_info(&self) -> Option<TranslationTableInfo> {
        if self.translation_in_symbolic_execution {
	    assert!(!self.run_in_el0()); // TODO: try out translation in symbolic execution in EL0
            let tt_base: u64 = 0x0000_0000_1040_0000;
            let entry: u64 = 0x3000_0000_0000_0701;
	    
            Some((tt_base..tt_base+4096, tt_base, entry))
        } else {
            None
        }
    }
    fn init<'ir, B: BV>(
        &self,
        shared_state: &SharedState<'ir, B>,
        local_frame: &mut LocalFrame<B>,
        solver: &mut Solver<B>,
        init_pc: u64,
        regs: HashMap<String, Sym>,
    ) {
        use isla_lib::ir::*;
        match local_frame.lets().get(&shared_state.symtab.lookup("z__a64_version")) {
            Some(UVal::Init(Val::String(s))) => println!("Model version {}", s),
            Some(v) => println!("Unexpected model version value {:?}", v),
            None => println!("No version information in model"),
        }

        if self.translation_in_symbolic_execution {
            let (_, tt_base, _) = self.translation_table_info().unwrap();
            for (reg, value, size) in
                [("TTBR0_EL3", tt_base, 64),
                 ("MAIR_EL3", 0xff, 64),
                 ("TCR_EL3", 0x0d001519, 32)].iter()
            {
                let id = shared_state.symtab.lookup(&zencode::encode(reg));
                let val = local_frame.regs_mut().get_mut(&id).unwrap();
                *val = UVal::Init(Val::Bits(B::new(*value, *size)));
            }
        }

	if self.run_in_el0() {
	    let pstate_id = shared_state.symtab.lookup("zPSTATE");
	    let el_id = shared_state.symtab.lookup("zEL");
	    let uao_id = shared_state.symtab.lookup("zUAO");
            let pstate = local_frame.regs_mut().get_mut(&pstate_id).unwrap();
	    match pstate {
		UVal::Init(Val::Struct(fields)) => {
		    *fields.get_mut(&el_id).unwrap() = Val::Bits(B::new(0, 2));
		    // UAO isn't interesting enough to bother with for now
		    *fields.get_mut(&uao_id).unwrap() = Val::Bits(B::new(0, 1));
		}
		_ => panic!("Unexpected value for PSTATE: {:?}", pstate),
	    }
	}
	
        if self.aarch64_compatible() {
            let pcc_id = shared_state.symtab.lookup("zPCC");
            let pcc = local_frame.regs_mut().get_mut(&pcc_id).unwrap();
            match pcc {
                UVal::Init(Val::Bits(bv)) => *pcc = UVal::Init(Val::Bits(bv.set_slice(0, B::new(init_pc, 64)))),
                _ => panic!("Unexpected value for PCC: {:?}", pcc),
            }
        }
        for (reg, v) in regs {
            use isla_lib::smt::smtlib::*;
            if self.aarch64_compatible() && reg.starts_with("_R") {
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Extract(128, 64, Box::new(Exp::Var(v)))),
                    Box::new(Exp::Bits(vec![false; 129 - 64])),
                )));
            }
            if reg == "CPTR_EL3" {
                let mut mask = 0x3feff8ff;

                // Enable Morello iff !aarch64_compatible (strictly required by the current Morello harness)
                mask |= 0x00000200;
                let fixed = if self.aarch64_compatible() { 0x00000000 } else { 0x00000200 };

                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Bvand(Box::new(Exp::Bits64(mask, 32)), Box::new(Exp::Var(v)))),
                    Box::new(Exp::Bits64(fixed, 32)),
                )));
            }
            if reg == "SCTLR_EL3" {
                let reserved_mask =  0b1111_1111_1111_1111_1110_0100_1100_1111_0011_0101_1001_0111_1100_0111_1011_0000;
                let reserved_vals =  0b0000_0000_0000_0000_0000_0000_0000_0000_0011_0000_1000_0101_0000_0000_0011_0000;
                let fixed_mask = 0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0010_0000_0000_0001_0000_0000_0101;
                let fixed_vals =
                    if self.translation_in_symbolic_execution {
                        // Little endian at EL3, EL3 instructions cachable, EL3 cachable, EL3 stage 1 translation enabled
                        0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001_0000_0000_0101
                    } else {
                        // Little endian at EL3, EL3 instructions non-cachable, EL3 non-cachable, EL3 stage 1 translation disabled
                        0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
                    };
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Bvand(
                        Box::new(Exp::Bits64(
                            reserved_mask | fixed_mask,
                            64,
                        )),
                        Box::new(Exp::Var(v)),
                    )),
                    Box::new(Exp::Bits64(
                        reserved_vals | fixed_vals,
                        64,
                    )),
                )));
                // TODO: other RES bits due to unimplemented extensions
            }
	    if reg == "SCTLR_EL1" {
		// TODO: allow variation
		if self.translation_in_symbolic_execution {
		    solver.add(Def::Assert(Exp::Eq(Box::new(Exp::Var(v)),
						   Box::new(Exp::Bits64(0x31c5d505, 64)))));
		} else {
		    solver.add(Def::Assert(Exp::Eq(Box::new(Exp::Var(v)),
						   Box::new(Exp::Bits64(0x31c5d504, 64)))));
		}
	    }
            if reg == "CCTLR_EL3" {
                let mask: u64 = 0xffff_ff02
                    | 0b1 // fix page table tag generation bit (want to avoid unnecessary fork)
                    | 0b10000; // Leave C64E = 0 for the harness
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Bvand(Box::new(Exp::Bits64(mask, 32)), Box::new(Exp::Var(v)))),
                    Box::new(Exp::Bits64(0, 32)),
                )));
            }
            if reg == "PCC" {
                assert!(!self.aarch64_compatible());
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Extract(63, 0, Box::new(Exp::Var(v)))),
                    Box::new(Exp::Bits64(init_pc, 64)))));
                // The harness needs the PCC to have the executive permission for now
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Extract(111, 111, Box::new(Exp::Var(v)))),
                    Box::new(Exp::Bits64(1, 1)))));
            }
        }
    }
    fn postprocess<'ir, B: BV>(&self,
        _shared_state: &SharedState<'ir, B>,
        _frame: &LocalFrame<B>,
        _solver: &mut Solver<B>,
    ) -> Result<(), String> {
        Ok(())
    }
    fn is_gpr(name: &str) -> Option<u32> {
        if name.starts_with("z_R") {
            let reg_str = &name[3..];
            u32::from_str_radix(reg_str, 10).ok()
        } else {
            None
        }
    }
    fn gpr_prefix() -> &'static str {
        "z_R"
    }
    fn gpr_pad() -> bool {
        true
    }
    fn run_instruction_function() -> String {
        "step_model".to_string()
    }
    fn has_capabilities(&self) -> bool {
        !self.aarch64_compatible()
    }
    fn run_in_el0(&self) -> bool {
	match self.style {
	    MorelloStyle::EL0 => true,
	    _ => false,
	}
    }
    fn final_instruction(&self, exit_register: u32) -> u32 {
        use MorelloStyle::*;
        match self.style {
            AArch64Compatible => 0xd61f0000 | (exit_register << 5), // br exit_register
            EL3Only => 0b11_0000101100_00100_0_0_100_00000_0_0_0_00 | (exit_register << 5), // br exit_capability
	    EL0 => 0xd4000001, // SVC 0
        }
    }
}
