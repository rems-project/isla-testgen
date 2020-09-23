use std::collections::HashMap;

use isla_lib::concrete::BV;
use isla_lib::executor::LocalFrame;
use isla_lib::ir::{SharedState, UVal, Val};
use isla_lib::smt::{Solver, Sym};
use isla_lib::smt::smtlib::{Def, Exp};

use crate::extract_state::GVAccessor;

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
    fn final_instruction(&self, exit_register: u32) -> u32 {
        0xd61f0000 | (exit_register << 5) // br exit_register
    }
}

pub struct Morello {
    pub aarch64_compatible: bool,
}

impl Target for Morello {
    fn regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)> {
        let mut regs: Vec<(String, Vec<GVAccessor<String>>)> =
            (0..31).map(|r| (format!("_R{:02}", r), vec![])).collect();
        let mut vector_regs = (0..31).map(|i| ("_V".to_string(), vec![GVAccessor::Element(i)])).collect();
        let mut other_regs =
            ["_PC", "SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3"].iter().map(|r| (r.to_string(), vec![])).collect();
        let mut flags = ["N", "Z", "C", "V"]
            .iter()
            .map(|flag| ("PSTATE".to_string(), vec![GVAccessor::Field(flag.to_string())]))
            .collect();
        let mut sys_regs: Vec<(String, Vec<GVAccessor<String>>)> =
            ["CPTR_EL3", "SCTLR_EL3"].iter().map(|r| (r.to_string(), vec![])).collect();
        if !self.aarch64_compatible {
            sys_regs.push(("CCTLR_EL3".to_string(), vec![]));
            sys_regs.push(("PSTATE".to_string(), vec![GVAccessor::Field("C64".to_string())]));
            sys_regs.push(("PCC".to_string(), vec![]));
        }
        regs.append(&mut vector_regs);
        regs.append(&mut other_regs);
        regs.append(&mut flags);
        regs.append(&mut sys_regs);
        regs
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
        if self.aarch64_compatible {
            let pcc_id = shared_state.symtab.lookup("zPCC");
            let pcc = local_frame.regs_mut().get_mut(&pcc_id).unwrap();
            match pcc {
                UVal::Init(Val::Bits(bv)) => *pcc = UVal::Init(Val::Bits(bv.set_slice(0, B::new(init_pc, 64)))),
                _ => panic!("Unexpected value for PCC: {:?}", pcc),
            }
        }
        for (reg, v) in regs {
            use isla_lib::smt::smtlib::*;
            if self.aarch64_compatible && reg.starts_with("_R") {
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Extract(128, 64, Box::new(Exp::Var(v)))),
                    Box::new(Exp::Bits(vec![false; 129 - 64])),
                )));
            }
            if reg == "CPTR_EL3" {
                let mut mask = 0x3feff8ff;
                if self.aarch64_compatible {
                    mask |= 0x00000200
                };
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Bvand(Box::new(Exp::Bits64(mask, 32)), Box::new(Exp::Var(v)))),
                    Box::new(Exp::Bits64(0x00000000, 32)),
                )));
            }
            if reg == "SCTLR_EL3" {
                let reserved_mask = 0b1111_1111_1111_1111_1110_0100_1100_1111_0011_0101_1001_0111_1100_0111_1011_0000;
                let reserved_vals = 0b0000_0000_0000_0000_0000_0000_0000_0000_0011_0000_1000_0101_0000_0000_0011_0000;
                // Little endian at EL3, EL3 instructions non-cachable, EL3 non-cachable, EL3 stage 1 translation disabled
                let fixed_mask =    0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0010_0000_0000_0001_0000_0000_0101;
                let fixed_vals =    0b0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;
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
            if reg == "CCTLR_EL3" {
                let mask: u64 = 0xffff_ff02 | 0b10000; // Leave C64E = 0 for the harness
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Bvand(Box::new(Exp::Bits64(mask, 32)), Box::new(Exp::Var(v)))),
                    Box::new(Exp::Bits64(0, 32)),
                )));
            }
            if reg == "PCC" {
                assert!(!self.aarch64_compatible);
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
        shared_state: &SharedState<'ir, B>,
        frame: &LocalFrame<B>,
        solver: &mut Solver<B>,
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
        !self.aarch64_compatible
    }
    fn final_instruction(&self, exit_register: u32) -> u32 {
        if self.aarch64_compatible {
            0xd61f0000 | (exit_register << 5) // br exit_register
        } else {
            0b11_0000101100_00100_0_0_100_00000_0_0_0_00 | (exit_register << 5) // br exit_capability
        }
    }
}
