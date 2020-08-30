use std::collections::HashMap;

use isla_lib::concrete::BV;
use isla_lib::executor::LocalFrame;
use isla_lib::ir::SharedState;
use isla_lib::smt::{Solver, Sym};

use crate::extract_state::GVAccessor;

pub trait Target {
    /// Registers supported by the test harness
    fn regs() -> Vec<(String, Vec<GVAccessor<String>>)>;
    /// Any additional initialisation
    fn init<'ir, B: BV>(
        shared_state: &SharedState<'ir, B>,
        frame: &mut LocalFrame<B>,
        solver: &mut Solver<B>,
        init_pc: u64,
        regs: HashMap<String, Sym>,
    );
    fn is_gpr(name: &str) -> Option<u32>;
    fn gpr_prefix() -> &'static str;
    fn gpr_pad() -> bool;
    // I'd like to move the stuff below to the config
    fn run_instruction_function() -> String;
}

pub struct Aarch64 {}

impl Target for Aarch64 {
    fn regs() -> Vec<(String, Vec<GVAccessor<String>>)> {
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
}

pub struct Morello {}

impl Target for Morello {
    fn regs() -> Vec<(String, Vec<GVAccessor<String>>)> {
        let mut regs: Vec<(String, Vec<GVAccessor<String>>)> =
            (0..31).map(|r| (format!("_R{:02}", r), vec![])).collect();
        let mut vector_regs = (0..31).map(|i| ("_V".to_string(), vec![GVAccessor::Element(i)])).collect();
        let mut other_regs =
            ["_PC", "SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3"].iter().map(|r| (r.to_string(), vec![])).collect();
        let mut flags = ["N", "Z", "C", "V"]
            .iter()
            .map(|flag| ("PSTATE".to_string(), vec![GVAccessor::Field(flag.to_string())]))
            .collect();
        let mut sys_regs = ["CPTR_EL3", "SCTLR_EL3"].iter().map(|r| (r.to_string(), vec![])).collect();
        regs.append(&mut vector_regs);
        regs.append(&mut other_regs);
        regs.append(&mut flags);
        regs.append(&mut sys_regs);
        regs
    }
    fn init<'ir, B: BV>(
        shared_state: &SharedState<'ir, B>,
        local_frame: &mut LocalFrame<B>,
        solver: &mut Solver<B>,
        init_pc: u64,
        regs: HashMap<String, Sym>,
    ) {
        use isla_lib::ir::*;
        let pcc_id = shared_state.symtab.lookup("zPCC");
        let pcc = local_frame.regs_mut().get_mut(&pcc_id).unwrap();
        match pcc {
            UVal::Init(Val::Bits(bv)) => *pcc = UVal::Init(Val::Bits(bv.set_slice(0, B::new(init_pc, 64)))),
            _ => panic!("Unexpected value for PCC: {:?}", pcc),
        }
        for (reg, v) in regs {
            use isla_lib::smt::smtlib::*;
            if reg.starts_with("_R") {
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Extract(128, 64, Box::new(Exp::Var(v)))),
                    Box::new(Exp::Bits(vec![false; 129 - 64])),
                )));
            }
            if reg == "CPTR_EL3" {
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Bvand(Box::new(Exp::Bits64(0x3feffaff, 32)), Box::new(Exp::Var(v)))),
                    Box::new(Exp::Bits64(0x00000000, 32)),
                )));
            }
            if reg == "SCTLR_EL3" {
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Bvand(
                        Box::new(Exp::Bits64(
                            0b1111_1111_1111_1111_1110_0100_1100_1111_0011_0101_1001_0111_1100_0111_1011_0000,
                            64,
                        )),
                        Box::new(Exp::Var(v)),
                    )),
                    Box::new(Exp::Bits64(
                        0b0000_0000_0000_0000_0000_0000_0000_0000_0011_0000_1000_0101_0000_0000_0011_0000,
                        64,
                    )),
                )));
                // TODO: other RES bits due to unimplemented extensions
            }
        }
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
}
