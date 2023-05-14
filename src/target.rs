// BSD 2-Clause License
//
// Copyright (c) 2020, 2021, 2022 Brian Campbell
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
use std::collections::HashMap;
use std::ops::Range;

use isla_lib::bitvector::{BV, b64::B64};
use isla_lib::executor::LocalFrame;
use isla_lib::ir::{Name, SharedState, Ty, Val};
use isla_lib::primop_util::smt_value;
use isla_lib::smt;
use isla_lib::smt::{smtlib, Solver, Sym};
use isla_lib::smt::smtlib::{bits64, Exp};
use isla_lib::source_loc::SourceLoc;
use isla_lib::zencode;

use crate::execution;
use crate::extract_state::GVAccessor;

// For now we only need one entry in the translation table (and only
// for Morello), so this is (address range, entry address, entry data).
pub type TranslationTableInfo = (Range<u64>, u64, u64);

pub trait Target
where
    Self: Sync,
{
    /// Model initialisation function
    fn init_function(&self) -> String;
    /// Test start address
    fn init_pc(&self) -> u64;
    /// Registers supported by the test harness
    fn regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)>;
    /// Registers that the harness wants even if they're not in the trace
    fn essential_regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)>;
    /// System registers that the harness should check
    fn post_regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)>;
    /// Special setup for some registers
    fn special_reg_init<'ctx, 'ir, B: BV>(
        &self,
        reg: &str,
        acc: &Vec<GVAccessor<String>>,
        ty: &Ty<Name>,
        shared_state: &SharedState<'ir, B>,
        frame: &mut LocalFrame<'ir, B>,
        ctx: &'ctx smt::Context,
        solver: &mut Solver<'ctx, B>,
    ) -> Option<(Sym, Val<B>)>;
    /// Special encoding for some registers in post-state
    fn special_reg_encode<'ctx, 'ir, B: BV>(
        &self,
        reg: &str,
        acc: &Vec<GVAccessor<String>>,
        ty: &Ty<Name>,
        shared_state: &SharedState<'ir, B>,
        frame: &mut LocalFrame<'ir, B>,
        ctx: &'ctx smt::Context,
        solver: &mut Solver<'ctx, B>,
    ) -> Option<Val<B>>;
    /// Any additional initialisation
    fn init<'ir, B: BV>(
        &self,
        shared_state: &SharedState<'ir, B>,
        frame: &mut LocalFrame<'ir, B>,
        solver: &mut Solver<B>,
        init_pc: u64,
        regs: &HashMap<(String, Vec<GVAccessor<String>>), Sym>,
    );
    fn post_instruction<'ir, B: BV>(
        &self,
        shared_state: &SharedState<'ir, B>,
        frame: &mut LocalFrame<'ir, B>,
        solver: &mut Solver<B>,
    );
    fn translation_table_info(&self) -> Option<TranslationTableInfo>;
    fn pc_alignment_pow() -> u32;
    fn pc_reg(&self) -> (String, Vec<GVAccessor<String>>);
    fn number_gprs() -> u32;
    fn is_gpr(name: &str) -> Option<u32>;
    fn gpr_prefix() -> &'static str;
    fn gpr_pad() -> bool;
    fn exception_stop_functions() -> Vec<String>;
    fn postprocess<'ir, B: BV>(&self,
        shared_state: &SharedState<'ir, B>,
        frame: &LocalFrame<B>,
        solver: &mut Solver<B>,
    ) -> Result<(), String>;
    fn has_capabilities(&self) -> bool;
    fn run_in_el0(&self) -> bool;
    // I'd like to move the stuff below to the config
    fn run_instruction_function() -> String;
    fn final_instruction<B: BV>(&self, exit_register: u32) -> B;
}

pub struct Aarch64 {}

impl Target for Aarch64 {
    fn init_function(&self) -> String {
        String::from("init")
    }

    fn init_pc(&self) -> u64 {
        0x400000
    }

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
    fn essential_regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)> {
        vec![]
    }
    fn post_regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)> { vec![] }
    fn special_reg_init<'ctx, 'ir, B: BV>(
        &self,
        _reg: &str,
        _acc: &Vec<GVAccessor<String>>,
        _ty: &Ty<Name>,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<'ir, B>,
        _ctx: &'ctx smt::Context,
        _solver: &mut Solver<'ctx, B>,
    ) -> Option<(Sym, Val<B>)> { None }
    fn special_reg_encode<'ctx, 'ir, B: BV>(
        &self,
        _reg: &str,
        _acc: &Vec<GVAccessor<String>>,
        _ty: &Ty<Name>,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<'ir, B>,
        _ctx: &'ctx smt::Context,
        _solver: &mut Solver<'ctx, B>,
    ) -> Option<Val<B>> { None }
    fn init<'ir, B: BV>(
        &self,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<B>,
        _solver: &mut Solver<B>,
        _init_pc: u64,
        _regs: &HashMap<(String, Vec<GVAccessor<String>>), Sym>,
    ) {
    }
    fn post_instruction<'ir, B: BV>(
        &self,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<'ir, B>,
        _solver: &mut Solver<B>,
    ) {}
    fn translation_table_info(&self) -> Option<TranslationTableInfo> {
        None
    }
    fn pc_alignment_pow() -> u32 { 2 }
    fn pc_reg(&self) -> (String, Vec<GVAccessor<String>>) { (String::from("z_PC"), vec![]) }
    fn number_gprs() -> u32 { 31 }
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
    fn exception_stop_functions() -> Vec<String> {
        vec!["AArch64_TakeException".to_string(),
//             "AArch64_TakeException,post_toplevel_check".to_string(),
        ]
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
    fn final_instruction<B: BV>(&self, exit_register: u32) -> B {
        B::from_u32(0xd61f0000 | (exit_register << 5)) // br exit_register
    }
}

#[derive(Clone,Copy)]
pub enum MorelloStyle { AArch64Compatible, EL3Only, EL0 }

pub struct Morello {
    pub style: MorelloStyle,
    pub translation_in_symbolic_execution: bool,
}

pub fn translation_table_exp(tt_info: &TranslationTableInfo, read_exp: smtlib::Exp<Sym>, addr_exp: smtlib::Exp<Sym>, bytes: u32) -> smtlib::Exp<Sym> {
    let (addresses, tt_base, entry) = tt_info;
    let tt_base = *tt_base;
    let entry = *entry;
    use smtlib::Exp::{And, Ite, Eq, Bvule, Bvult};

    let bits = 8 * bytes;
    let mask: u64 = 0xffffffffffffffff >> 64 - bits;
    let address_prop = And(Box::new(Bvule(Box::new(bits64(addresses.start, 64)), Box::new(addr_exp.clone()))),
                           Box::new(Bvult(Box::new(addr_exp.clone()), Box::new(bits64(addresses.end, 64)))));
    let value_exp =
        Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(bits64(tt_base, 64)))),
            Box::new(bits64(entry & mask, bits)),
            Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(bits64(tt_base + 1, 64)))),
                         Box::new(bits64((entry >> 8) & mask, bits)),
                         Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(bits64(tt_base + 2, 64)))),
                                      Box::new(bits64((entry >> 16) & mask, bits)),
                                      Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(bits64(tt_base + 3, 64)))),
                                                   Box::new(bits64((entry >> 24) & mask, bits)),
                                                   Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(bits64(tt_base + 4, 64)))),
                                                                Box::new(bits64((entry >> 32) & mask, bits)),
                                                                Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(bits64(tt_base + 5, 64)))),
                                                                             Box::new(bits64((entry >> 40) & mask, bits)),
                                                                             Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(bits64(tt_base + 6, 64)))),
                                                                                          Box::new(bits64((entry >> 48) & mask, bits)),
                                                                                          Box::new(Ite(Box::new(Eq(Box::new(addr_exp.clone()), Box::new(bits64(tt_base + 7, 64)))),
                                                                                                       Box::new(bits64((entry >> 56) & mask, bits)),
                                                                                                       Box::new(bits64(0, bits)))))))))))))))));
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
    fn init_function(&self) -> String {
        String::from("__InitSystem")
    }

    fn init_pc(&self) -> u64 {
        0x40400000
    }
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
            sys_regs.push(("CSCR_EL3".to_string(), vec![]));
        }
	if self.run_in_el0() {
	    sys_regs.push(("PSTATE".to_string(), vec![GVAccessor::Field("EL".to_string())]));
	    sys_regs.push(("SCTLR_EL1".to_string(), vec![]));
	    sys_regs.push(("CPACR_EL1".to_string(), vec![]));
            sys_regs.push(("CCTLR_EL1".to_string(), vec![]));
            sys_regs.push(("CCTLR_EL0".to_string(), vec![]));
            sys_regs.push(("DDC_EL0".to_string(), vec![]));
            sys_regs.push(("DDC_EL1".to_string(), vec![]));
            // NB: the harness uses a different value for VBAR_EL1, then jumps to this
	    sys_regs.push(("VBAR_EL1".to_string(), vec![]));
            sys_regs.push(("HCR_EL2".to_string(), vec![]));
	}
        regs.append(&mut vector_regs);
        regs.append(&mut other_regs);
        regs.append(&mut flags);
        regs.append(&mut sys_regs);
        regs
    }
    fn post_regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)> {
        let mut regs: Vec<(String, Vec<GVAccessor<String>>)> =
            ["SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3"].iter().map(|r| (r.to_string(), vec![])).collect();
        if self.run_in_el0() {
            regs.push(("PCC".to_string(), vec![]));
            regs.push(("ESR_EL1".to_string(), vec![]));
        }
        regs
    }
    fn essential_regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)> {
	if self.run_in_el0() {
	    vec![("CPACR_EL1".to_string(), vec![]), ("HCR_EL2".to_string(), vec![]), ("CCTLR_EL1".to_string(), vec![]), ("VBAR_EL1".to_string(), vec![])]
        } else {
            vec![]
        }
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
    fn special_reg_init<'ctx, 'ir, B: BV>(
        &self,
        _reg: &str,
        _acc: &Vec<GVAccessor<String>>,
        _ty: &Ty<Name>,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<'ir, B>,
        _ctx: &'ctx smt::Context,
        _solver: &mut Solver<'ctx, B>,
    ) -> Option<(Sym, Val<B>)> { None }
    fn special_reg_encode<'ctx, 'ir, B: BV>(
        &self,
        _reg: &str,
        _acc: &Vec<GVAccessor<String>>,
        _ty: &Ty<Name>,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<'ir, B>,
        _ctx: &'ctx smt::Context,
        _solver: &mut Solver<'ctx, B>,
    ) -> Option<Val<B>> { None }
    fn init<'ir, B: BV>(
        &self,
        shared_state: &SharedState<'ir, B>,
        local_frame: &mut LocalFrame<'ir, B>,
        solver: &mut Solver<B>,
        init_pc: u64,
        regs: &HashMap<(String, Vec<GVAccessor<String>>), Sym>,
    ) {
        use isla_lib::ir::*;
        match local_frame.lets().get(&shared_state.symtab.lookup("z__a64_version")) {
            Some(UVal::Init(Val::String(s))) => println!("Model version {}", s),
            Some(v) => println!("Unexpected model version value {:?}", v),
            None => println!("No version information in model"),
        }

        if self.translation_in_symbolic_execution {
            let (_, tt_base, _) = self.translation_table_info().unwrap();
            for (reg, value) in
                [("TTBR0_EL3", B::new(tt_base, 64)),
                 ("MAIR_EL3", B::new(0xff, 64)),
                 ("TCR_EL3", B::new(0x0d001519, 32))].iter()
            {
                let id = shared_state.symtab.lookup(&zencode::encode(reg));
                local_frame.regs_mut().assign(id, Val::Bits(*value), shared_state);
            }
        }

	if self.run_in_el0() {
	    let pstate_id = shared_state.symtab.lookup("zPSTATE");
	    let el_id = shared_state.symtab.lookup("zEL");
	    let uao_id = shared_state.symtab.lookup("zUAO");
            let pstate = local_frame.regs().get_last_if_initialized(pstate_id);
	    match pstate {
		Some(Val::Struct(fields)) => {
                    let mut fields = fields.clone();
		    *fields.get_mut(&el_id).unwrap() = Val::Bits(B::new(0, 2));
		    // UAO isn't interesting enough to bother with for now
		    *fields.get_mut(&uao_id).unwrap() = Val::Bits(B::new(0, 1));
                    local_frame.regs_mut().assign(pstate_id, Val::Struct(fields), shared_state);
		}
		_ => panic!("Unexpected value for PSTATE: {:?}", pstate),
	    }
            for (reg, value) in
                [// Set RW, although SCR_EL3.RW should be enough
                 ("HCR_EL2", B::new(0x8000_0000, 64)),
                 ].iter()
            {
                let id = shared_state.symtab.lookup(&zencode::encode(reg));
                local_frame.regs_mut().assign(id, Val::Bits(*value), shared_state);
            }
	}
	
        if self.aarch64_compatible() {
            let pcc_id = shared_state.symtab.lookup("zPCC");
            let pcc = local_frame.regs().get_last_if_initialized(pcc_id);
            let pcc = match pcc {
                Some(Val::Bits(bv)) => Val::Bits(bv.set_slice(0, B::new(init_pc, 64))),
                _ => panic!("Unexpected value for PCC: {:?}", pcc),
            };
            local_frame.regs_mut().assign(pcc_id, pcc, shared_state);
        }
        for ((reg, _acc), v) in regs {
            use isla_lib::smt::smtlib::*;
            if self.aarch64_compatible() && reg.starts_with("_R") {
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Extract(128, 64, Box::new(Exp::Var(*v)))),
                    Box::new(Exp::Bits(vec![false; 129 - 64])),
                )));
            }
            if reg == "CPTR_EL3" {
                let mut mask = 0x3feff8ff;

                // Enable Morello iff !aarch64_compatible (strictly required by the current Morello harness)
                mask |= 0x00000200;
                let fixed = if self.aarch64_compatible() { 0x00000000 } else { 0x00000200 };

                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Bvand(Box::new(bits64(mask, 32)), Box::new(Exp::Var(*v)))),
                    Box::new(bits64(fixed, 32)),
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
                        Box::new(bits64(
                            reserved_mask | fixed_mask,
                            64,
                        )),
                        Box::new(Exp::Var(*v)),
                    )),
                    Box::new(bits64(
                        reserved_vals | fixed_vals,
                        64,
                    )),
                )));
                // TODO: other RES bits due to unimplemented extensions
            }
	    if reg == "SCTLR_EL1" {
		// TODO: allow variation
                // Note that alignment checking needs to be on if we're lying about address
                // translation, because without the MMU the memory will appear to be Device
                // Memory and the translation stub checks that all accesses are aligned.
		if self.translation_in_symbolic_execution {
		    solver.add(Def::Assert(Exp::Eq(Box::new(Exp::Var(*v)),
						   Box::new(bits64(0x30d5d985, 64)))));
		} else {
		    solver.add(Def::Assert(Exp::Eq(Box::new(Exp::Var(*v)),
						   Box::new(bits64(0x30d5d99e, 64)))));
		}
	    }
            if reg == "CCTLR_EL3" {
                let mask: u64 = 0xffff_ff02
                    | 0b1 // fix page table tag generation bit (want to avoid unnecessary fork)
                    | 0b10000; // Leave C64E = 0 for the harness
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Bvand(Box::new(bits64(mask, 32)), Box::new(Exp::Var(*v)))),
                    Box::new(bits64(0, 32)),
                )));
            }
            if reg == "PCC" {
                assert!(!self.aarch64_compatible());
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Extract(63, 0, Box::new(Exp::Var(*v)))),
                    Box::new(bits64(init_pc, 64)))));
                // The harness needs the PCC to have the executive permission for now
                if !self.run_in_el0() {
                    solver.add(Def::Assert(Exp::Eq(
                        Box::new(Exp::Extract(111, 111, Box::new(Exp::Var(*v)))),
                        Box::new(bits64(1, 1)))));
                }
            }
            if reg == "CPACR_EL1" {
                // Force Morello on for EL0/1 for now (ensures that we can check the full PCC
                // from CELR_EL1)
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Extract(19, 18, Box::new(Exp::Var(*v)))),
                    Box::new(bits64(0b11, 2)))));
            }
            if reg == "VBAR_EL1" {
                // Keep it sufficiently aligned rather than making the harness do it
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Extract(10, 0, Box::new(Exp::Var(*v)))),
                    Box::new(bits64(0, 11)))));
                // Make the capability bounds use the value to avoid an annoying case split by not using internal exponent
                // TODO: make this configurable
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Extract(94, 94, Box::new(Exp::Var(*v)))),
                    Box::new(bits64(1, 1)))));
            }
            if reg == "CCTLR_EL1" {
                // RES0 fields; really just to ensure that the register appears in the SMT model
                solver.add(Def::Assert(Exp::Eq(
                    Box::new(Exp::Extract(31, 8, Box::new(Exp::Var(*v)))),
                    Box::new(bits64(0, 24)))));
            }
        }
    }
    fn post_instruction<'ir, B: BV>(
        &self,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<'ir, B>,
        _solver: &mut Solver<B>,
    ) {}
    fn exception_stop_functions() -> Vec<String> {
        vec!["AArch64_TakeException".to_string()]
    }
    fn postprocess<'ir, B: BV>(&self,
        _shared_state: &SharedState<'ir, B>,
        _frame: &LocalFrame<B>,
        _solver: &mut Solver<B>,
    ) -> Result<(), String> {
        Ok(())
    }
    fn pc_alignment_pow() -> u32 { 2 }
    fn pc_reg(&self) -> (String, Vec<GVAccessor<String>>) { (String::from("z_PC"), vec![]) }
    fn number_gprs() -> u32 { 31 }
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
    fn final_instruction<B: BV>(&self, exit_register: u32) -> B {
        use MorelloStyle::*;
        B::from_u32(match self.style {
            AArch64Compatible => 0xd61f0000 | (exit_register << 5), // br exit_register
            EL3Only => 0b11_0000101100_00100_0_0_100_00000_0_0_0_00 | (exit_register << 5), // br exit_capability
	    EL0 => 0xd4000001, // SVC 0
        })
    }
}

pub enum X86Style { Plain, Cap }

pub struct X86 {
    pub style: X86Style
}

const X86_GPRS : [&str; 16] = 
    ["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rsp", "rbp", 
     "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"];

const C86_REGS : [&str; 3] =
    ["ddc", "cfs", "cgs"];

impl X86 {
    fn common_regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)> {
        vec![
            (String::from("rflags"),vec![GVAccessor::Field(String::from("bits"))]),
            (String::from("rip"),vec![]),
        ]
    }
}

impl Target for X86 {
    /// Model initialisation function
    // Bit of a cheat; using this to get to 64bit mode, currently works because the
    // actual initialisation function is empty.
    fn init_function(&self) -> String {
        String::from("initialise_64_bit_mode")
    }
    /// Test start address
    fn init_pc(&self) -> u64 {
        // Appears to be the default I got from ld on Linux
        0x401000
    }
            
    /// Registers supported by the test harness
    fn regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)> {
        let mut regs: Vec<(String, Vec<GVAccessor<String>>)> =
            X86_GPRS
            .iter()
            .map(|r| (r.to_string(), vec![]))
            .collect();
        regs.append(&mut self.common_regs());
        match self.style {
            X86Style::Plain => (),
            X86Style::Cap =>
            for r in C86_REGS {
                regs.push((r.to_string(), vec![]));
            }
        };
        // TODO: remove hack (repeats rip with field name to ensure that the address is extracted in extract_state)
        match self.style {
            X86Style::Plain => (),
            X86Style::Cap => regs.push((String::from("rip"), vec![GVAccessor::Field(String::from("address"))])),
        };
        regs
    }
    /// Registers that the harness wants even if they're not in the trace
    fn essential_regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)> { vec![] }
    /// System registers that the harness should check
    fn post_regs(&self) -> Vec<(String, Vec<GVAccessor<String>>)> { self.common_regs() }
    fn special_reg_init<'ctx, 'ir, B: BV>(
        &self,
        _reg: &str,
        _acc: &Vec<GVAccessor<String>>,
        ty: &Ty<Name>,
        shared_state: &SharedState<'ir, B>,
        frame: &mut LocalFrame<'ir, B>,
        ctx: &'ctx smt::Context,
        solver: &mut Solver<'ctx, B>,
    ) -> Option<(Sym, Val<B>)> {
        // TODO: use accessor?
        match ty {
            Ty::Struct(struct_name) if shared_state.symtab.get("zCapability") == Some(*struct_name) => {
                let var = solver.declare_const(smtlib::Ty::BitVec(129), SourceLoc::unknown());
                let tag = solver.define_const(
                    Exp::Eq(Box::new(Exp::Extract(128, 128, Box::new(Exp::Var(var)))),
                            Box::new(Exp::Bits64(B64::new(1, 1)))),
                    SourceLoc::unknown());
                let content = solver.define_const(Exp::Extract(127, 0, Box::new(Exp::Var(var))), SourceLoc::unknown());
                let val = execution::run_function_solver(
                    shared_state,
                    frame,
                    ctx,
                    solver,
                    "memBitsToCapability",
                    vec![Val::Symbolic(tag), Val::Symbolic(content)]
                );
                Some((var, val))
            }
            _ => None
        }
    }
    fn special_reg_encode<'ctx, 'ir, B: BV>(
        &self,
        reg: &str,
        _acc: &Vec<GVAccessor<String>>,
        ty: &Ty<Name>,
        shared_state: &SharedState<'ir, B>,
        frame: &mut LocalFrame<'ir, B>,
        ctx: &'ctx smt::Context,
        solver: &mut Solver<'ctx, B>,
    ) -> Option<Val<B>> {
        // TODO: use accessor?
        let name = shared_state.symtab.get(&zencode::encode(&reg)).unwrap();
        match ty {
            Ty::Struct(struct_name) if shared_state.symtab.get("zCapability") == Some(*struct_name) => {
                let struct_val = frame.regs().get_last_if_initialized(name).unwrap().clone();
                let tag_name = shared_state.symtab.get("ztag").unwrap();
                let tag = match &struct_val {
                    Val::Struct(fields) => fields.get(&tag_name).unwrap().clone(),
                    _ => panic!("Capability register {} wasn't a struct", reg),
                };
                let tag = match tag {
                    Val::Bool(b) => Exp::Bits64(B64::new(if b { 1 } else { 0 }, 1)),
                    Val::Symbolic(v) => Exp::Ite(
                        Box::new(Exp::Var(v)),
                        Box::new(Exp::Bits64(B64::new(1,1))),
                        Box::new(Exp::Bits64(B64::new(0,1)))
                    ),
                    _ => panic!("Unexpected value for capability tag in {}: {:?}", reg, tag),
                };
                let content = execution::run_function_solver(
                    shared_state,
                    frame,
                    ctx,
                    solver,
                    "capToMemBits",
                    vec![struct_val]
                );
                let content = smt_value(&content, SourceLoc::unknown()).unwrap();
                let var = solver.define_const(Exp::Concat(Box::new(tag), Box::new(content)), SourceLoc::unknown());
                Some(Val::Symbolic(var))
            }
            _ => None
        }
    }
    /// Any additional initialisation
    fn init<'ir, B: BV>(
        &self,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<'ir, B>,
        _solver: &mut Solver<B>,
        _init_pc: u64,
        _regs: &HashMap<(String, Vec<GVAccessor<String>>), Sym>,
    ) { }
    fn post_instruction<'ir, B: BV>(
        &self,
        _shared_state: &SharedState<'ir, B>,
        _frame: &mut LocalFrame<'ir, B>,
        _solver: &mut Solver<B>,
    ) { }
    fn translation_table_info(&self) -> Option<TranslationTableInfo> { None }
    fn pc_alignment_pow() -> u32 { 0 }
    fn pc_reg(&self) -> (String, Vec<GVAccessor<String>>) {
        match self.style {
            X86Style::Plain => (String::from("zrip"), vec![]),
            X86Style::Cap => (String::from("zrip"), vec![GVAccessor::Field(String::from("address"))]),
        }
    }
    fn number_gprs() -> u32 { X86_GPRS.len() as u32 }
    fn is_gpr(name: &str) -> Option<u32> {
        let name = zencode::decode(name);
        X86_GPRS.iter().position(|&x| name == x).map(|i| i as u32)
    }
    fn gpr_prefix() -> &'static str { panic!("not implemented"); }
    fn gpr_pad() -> bool { panic!("not implemented"); }
    // Model currently uses Sail exception for processor exceptions
    fn exception_stop_functions() -> Vec<String> { vec![] }
    fn postprocess<'ir, B: BV>(&self,
        _shared_state: &SharedState<'ir, B>,
        _frame: &LocalFrame<B>,
        _solver: &mut Solver<B>,
    ) -> Result<(), String> {
        Ok(())
    }
    fn has_capabilities(&self) -> bool {
        match self.style {
            X86Style::Plain => false,
            X86Style::Cap => true,
        }
    }
    fn run_in_el0(&self) -> bool { panic!("not implemented"); }
    // I'd like to move the stuff below to the config
    fn run_instruction_function() -> String { String::from("x86_fetch_decode_execute") }
    // Note that the final instruction is just a dummy because we only
    // support gdb tests at the moment.  I used to use an INT3
    // breakpoint, but that causes gdbserver to report the wrong RIP
    fn final_instruction<B: BV>(&self, _exit_register: u32) -> B {
        B::new(0x90, 8) // NOP
    }
}
