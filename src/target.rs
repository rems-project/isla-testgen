use std::collections::HashMap;

use isla_lib::concrete::BV;
use isla_lib::executor::LocalFrame;
use isla_lib::ir::SharedState;
use isla_lib::smt::{Solver, Sym};

pub trait Target {
    /// Registers supported by the test harness
    fn regs() -> Vec<String>;
    /// Any additional initialisation
    fn init<'ir, B: BV>(
        shared_state: &SharedState<'ir, B>,
        frame: &mut LocalFrame<B>,
        solver: &mut Solver<B>,
        init_pc: u64,
        regs: HashMap<String, Sym>,
    );
    fn is_gpr(name: &str) -> Option<u32>;
    // I'd like to move the stuff below to the config
    fn run_instruction_function() -> String;
}

pub struct Aarch64 {}

impl Target for Aarch64 {
    fn regs() -> Vec<String> {
        let mut regs: Vec<String> = (0..31).map(|r| format!("R{}", r)).collect();
        let mut other_regs = ["SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3"].iter().map(|r| r.to_string()).collect();
        regs.append(&mut other_regs);
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
    fn run_instruction_function() -> String {
        "Step_CPU".to_string()
    }
}

pub struct Morello {}

impl Target for Morello {
    fn regs() -> Vec<String> {
        let mut regs: Vec<String> = (0..31).map(|r| format!("_R{:02}", r)).collect();
        let mut other_regs = ["_PC", "SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3"].iter().map(|r| r.to_string()).collect();
        regs.append(&mut other_regs);
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
    fn run_instruction_function() -> String {
        "step_model".to_string()
    }
}
