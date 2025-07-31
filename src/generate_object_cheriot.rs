// BSD 2-Clause License
//
// Copyright (c) 2020, 2021, 2022 Brian Campbell
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

use crate::extract_state::{GVAccessor, GroundVal, PrePostStates};
use crate::generate_object_common::*;
use crate::target::Target;

use isla_lib::bitvector::BV;
use isla_lib::config::ISAConfig;
use isla_lib::zencode;

use std::collections::{BTreeMap, HashMap};
use std::convert::TryFrom;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::Write;

#[derive(Debug)]
pub enum HarnessError {
    TooHard(String),
}
impl fmt::Display for HarnessError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:#?}", self)
    }
}
impl Error for HarnessError {}

fn write_bytes(asm_file: &mut File, bytes: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
    let mut zeros = 0;
    for line in bytes.chunks(16) {
        if line.iter().all(|b| *b == 0) {
            zeros += line.len();
        } else {
            if zeros > 0 {
                writeln!(asm_file, "\t.zero {}", zeros)?;
                zeros = 0;
            }
            write!(asm_file, "\t.byte")?;
            let mut byte_iter = line.iter();
            if let Some(byte) = byte_iter.next() {
                write!(asm_file, " {:#04x}", byte)?;
                for byte in byte_iter {
                    write!(asm_file, ", {:#04x}", byte)?;
                }
            }
            writeln!(asm_file)?;
        }
    }
    if zeros > 0 { writeln!(asm_file, "\t.zero {}", zeros)?; };
    Ok(())
}

// TODO: to common file?
fn get_numbered_registers<B: BV>(
    prefix: &str,
    pad: bool,
    max: u32,
    state: &HashMap<(&str, Vec<GVAccessor<&str>>), GroundVal<B>>,
) -> Vec<(u32, B)> {
    (0..max)
        .filter_map(|i| {
            let name = if pad { format!("{}{:02}", prefix, i) } else { format!("{}{}", prefix, i) };
            match state.get(&(&name, vec![])) {
                Some(GroundVal::Bits(bs,m)) => {
                    assert!(m.is_zero());
                    Some((i, *bs))
                }
                Some(v) => panic!("Register {} was expected to be a bitvector, found {}", name, v),
                None => None,
            }
        })
        .collect()
}

// TODO: to common file?
fn get_system_registers<B: BV, T: Target>(
    target: &T,
    regs: &[(String, Vec<GVAccessor<String>>)],
    state: &HashMap<(&str, Vec<GVAccessor<&str>>), GroundVal<B>>,
) -> Vec<(String, B)> {
    let (pc_reg, _pc_acc) = target.pc_reg();
    regs
        .iter()
        .filter_map(|(reg, acc)| {
            let zreg = zencode::encode(reg);
            if acc.is_empty() && T::is_gpr(&zreg).is_none() && zreg != pc_reg {
                match state.get(&(&zreg, vec![])) {
                    Some(GroundVal::Bits(bs,m)) => {
                        assert!(m.is_zero());
                        Some((reg.clone(), *bs))
                    }
                    Some(v) => panic!("System register {} was expected to be a bitvector, found {}", reg, v),
                    None => None
                }
            } else {
                None
            }
        })
        .collect()
}

fn get_exit_address<B: BV>(
    pre_post_states: &PrePostStates<B>,
) -> u64 {
    if let Some(GroundVal::Bits(final_pc,m)) = pre_post_states.post_registers.get(&("z_PC", vec![])) {
        assert!(m.is_zero());
        final_pc.lower_u64() + 4
    } else {
        panic!("Missing PC register in post state");
    }
}

fn write_main_memory<B: BV>(
    asm_file: &mut File,
    sections: &mut BTreeMap<u64, (String, Option<usize>)>,
    pre_post_states: &PrePostStates<B>,
    harness_data: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut name = 0;
    for (region, contents) in pre_post_states.pre_memory.iter() {
        sections.insert(region.start, (format!(".data{0}", name), Some(contents.len())));
        writeln!(asm_file, ".section .data{},\"aw\"", name)?;
        write_bytes(asm_file, contents)?;
        name += 1;
    }
    sections.insert(harness_data, (String::from(".data"), None));
    name = 0;
    for (_region, contents) in pre_post_states.post_memory.iter() {
        writeln!(asm_file, ".data")?;
        writeln!(asm_file, "check_data{}:", name)?;
        write_bytes(asm_file, contents)?;
        name += 1;
    }
    Ok(())
}

fn write_capability_data<B: BV, T: Target>(
    target: &T,
    asm_file: &mut File,
    gprs: &[(u32, B)],
    post_gprs: &[(u32, B)],
    system_registers: &[(String, B)],
    post_system_registers: &[(String, B)],
    pre_post_states: &PrePostStates<B>,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut extra_tags = vec![];
    writeln!(asm_file, ".data")?;
    writeln!(asm_file, ".balign 8")?;
    writeln!(asm_file, "initial_cap_values:")?;
    for (i, (reg, value)) in gprs.iter().enumerate() {
        let value_except_tag = value.slice(0, 64).unwrap();
        writeln!(asm_file, "\t/* C{} */", reg)?;
        writeln!(asm_file, "\t.dword {:#x}", value_except_tag)?;
        if !value.slice(64, 1).unwrap().is_zero() {
            extra_tags.push(format!("initial_cap_values + {}", i * 8));
        }
    }
    writeln!(asm_file, "final_cap_values:")?;
    for (i, (reg, value)) in post_gprs.iter().enumerate() {
        let value_except_tag = value.slice(0, 64).unwrap();
        writeln!(asm_file, "\t/* C{} */", reg)?;
        writeln!(asm_file, "\t.dword {:#x}", value_except_tag)?;
        if !value.slice(64, 1).unwrap().is_zero() {
            extra_tags.push(format!("final_cap_values + {}", i * 8));
        }
    }
    for (reg, value) in system_registers {
        let value_except_tag = value.slice(0, 64).unwrap();
        writeln!(asm_file, "initial_{}_value:", reg)?;
        writeln!(asm_file, "\t.dword {:#x}", value_except_tag)?;
        if !value.slice(64, 1).unwrap().is_zero() {
            extra_tags.push(format!("initial_{}_value", reg));
        }
    }
    for (reg, value) in post_system_registers {
        let value_except_tag = value.slice(0, 64).unwrap();
        writeln!(asm_file, "final_{}_value:", reg)?;
        writeln!(asm_file, "\t.dword {:#x}", value_except_tag)?;
        if !value.slice(64, 1).unwrap().is_zero() {
            extra_tags.push(format!("final_{}_value", reg));
        }
    }
    
    writeln!(asm_file, ".balign 8")?;
    writeln!(asm_file, "initial_tag_locations:")?;
    for (region, tags) in pre_post_states.pre_tag_memory.iter() {
        for (i, tag) in tags.iter().enumerate() {
            if *tag {
                writeln!(asm_file, "\t.word {:#010x}", region.start + i as u64)?;
            }
        }
    }
    for address in extra_tags {
        writeln!(asm_file, "\t.word {}", address)?;
    }
    writeln!(asm_file, "\t.word 0")?;

    writeln!(asm_file, "final_tag_set_locations:")?;
    for (addr, tag) in pre_post_states.post_tag_memory.iter() {
        if *tag {
            writeln!(asm_file, "\t.word {:#010x}", addr)?;
        }
    }
    writeln!(asm_file, "\t.dword 0")?;

    writeln!(asm_file, "final_tag_unset_locations:")?;
    for (addr, tag) in pre_post_states.post_tag_memory.iter() {
        if !*tag {
            writeln!(asm_file, "\t.word {:#010x}", addr)?;
        }
    }
    writeln!(asm_file, "\t.word 0")?;
    Ok(())
}

pub fn make_asm_files<B: BV, T: Target>(
    target: &T,
    base_name: &str,
    instr_map: &HashMap<B, String>,
    pre_post_states: PrePostStates<B>,
    harness_code: Option<u64>,
    harness_data: Option<u64>,
    uart: Option<u64>,
    entry_reg: u32,
    exit_reg: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    // Adjust spare register numbers for the zero register
    let entry_reg = entry_reg + 1;
    let exit_reg = exit_reg + 1;

    let harness_code = harness_code.unwrap_or(0x80000000);
    let harness_data = harness_data.unwrap_or(0x80000400);
    let uart = uart.unwrap_or(0x10000000);

    let mut asm_file = File::create(&format!("{}.s", base_name))?;
    let mut sections: BTreeMap<u64, (String, Option<usize>)> = BTreeMap::new();

    let gprs = get_numbered_registers(T::gpr_prefix(), T::gpr_pad(), 15, &pre_post_states.pre_registers);
    let post_gprs = get_numbered_registers(T::gpr_prefix(), T::gpr_pad(), 15, &pre_post_states.post_registers);
    let system_registers = get_system_registers(target, &target.regs(), &pre_post_states.pre_registers);
    let post_system_registers = get_system_registers(target, &target.post_regs(), &pre_post_states.post_registers);

    let mut name = 0;
    for (region, contents) in pre_post_states.code.iter() {
        sections.insert(region.start, (format!(".text{0}", name), None));
        writeln!(asm_file, ".section .text{},\"ax\"", name)?;
        if name == 0 {
            writeln!(asm_file, "test_start:")?;
        }
        let mut zeros = 0;
        let mut addr = region.start;
        // .insn isn't in the current CHERIoT LLVM and we have both 2 and 4 byte instructions,
        // so just keep it simple and output bytes
        for byte in contents {
            if *byte == 0 {
                zeros += 1;
            } else {
                if zeros > 0 { writeln!(asm_file, "\t.zero {}", zeros)?; };
                zeros = 0;
                write!(asm_file, "\t.byte {:#04x}", byte)?;
                if let Some(description) = pre_post_states.instruction_locations.get(&addr) {
                    writeln!(asm_file, " // {}", description)?;
                } else {
                    writeln!(asm_file)?;
                }
            }
            addr += 1;
        }
        if zeros > 0 { writeln!(asm_file, "\t.zero {}", zeros)?; };
        name += 1;
    }

    writeln!(asm_file, "")?;
    write_main_memory(&mut asm_file, &mut sections, &pre_post_states, harness_data)?;

    if target.has_capabilities() {
    writeln!(asm_file, "")?;
        write_capability_data(target, &mut asm_file, &gprs, &post_gprs, &system_registers, &post_system_registers, &pre_post_states)?;
    }
    writeln!(asm_file, "")?;

    // Adapted from a macro in the cheriot-rtos bootloader
    // Assumes the root memory cap is in c1
    writeln!(asm_file, ".macro cla_abs reg, src, symbol")?;
    writeln!(asm_file, "\tlui x\\reg, %hi(\\symbol)")?;
    writeln!(asm_file, "\taddi x\\reg, x\\reg, %lo(\\symbol)")?;
    writeln!(asm_file, "\tcsetaddr c\\reg, \\src, x\\reg")?;
    writeln!(asm_file, ".endmacro")?;

    sections.insert(harness_code, (String::from(".text"), None));

    writeln!(asm_file, ".text")?;
    writeln!(asm_file, ".global preamble")?;
    writeln!(asm_file, "preamble:")?;


    writeln!(asm_file, "\t/* Write tags to memory */")?;
    writeln!(asm_file, "\tcspecialr c1, mtdc")?;
    writeln!(asm_file, "\tcspecialr c2, mscratchc")?;
    writeln!(asm_file, "\tcla_abs 3, c1, initial_tag_locations")?;
    writeln!(asm_file, "\tli x12, 0xffffffff")?;
    writeln!(asm_file, "tag_init_loop:")?;
    writeln!(asm_file, "\tclw x4, 0(c3)")?;
    writeln!(asm_file, "\tbeq x4, zero, tag_init_end")?;
    writeln!(asm_file, "\tcsetaddr c4, c1, x4")?;
    writeln!(asm_file, "\tclc c5, 0(c4)")?;
    writeln!(asm_file, "\tcgetperm x6, c5")?;
    writeln!(asm_file, "\tcgettype x7, c5")?;
    writeln!(asm_file, "\tcgetbase x8, c5")?;
    writeln!(asm_file, "\tcgetlen  x9, c5")?;
    writeln!(asm_file, "\tcgetaddr x10, c5")?;
    writeln!(asm_file, "\t/* choose root */")?;
    writeln!(asm_file, "\tand x11, x6, 0x100")?;
    writeln!(asm_file, "\tbne x11, zero, use_exe_root")?;
    writeln!(asm_file, "\tsrli x11, x6, 8")?;
    writeln!(asm_file, "\tand x11, x11, 0xe")?;
    writeln!(asm_file, "\tbne x11, zero, use_seal_root")?;
    writeln!(asm_file, "\t/* mem root */")?;
    writeln!(asm_file, "\tcmove c11, c1")?;
    writeln!(asm_file, "\tj root_loaded")?;
    writeln!(asm_file, "use_exe_root:")?;
    writeln!(asm_file, "\tcspecialr c11, mtcc")?;
    writeln!(asm_file, "\tj root_loaded")?;
    writeln!(asm_file, "use_seal_root:")?;
    writeln!(asm_file, "\tcmove c11, c2")?;
    writeln!(asm_file, "root_loaded:")?;
    writeln!(asm_file, "\t/* skip bounds setting if whole address space */")?;
    writeln!(asm_file, "\tbeq x9, x12, bounds_set")?;
    writeln!(asm_file, "\tcsetaddr c11, c11, x8")?;
    writeln!(asm_file, "\tcsetboundsexact c11, c11, x9")?;
    writeln!(asm_file, "bounds_set:")?;
    writeln!(asm_file, "\tcsetaddr c11, c11, x10")?;
    writeln!(asm_file, "\tcandperm c11, c11, x6")?;
    writeln!(asm_file, "\tbeq x7, zero, skip_seal")?;
    writeln!(asm_file, "\tcsetaddr c2, c2, x7")?;
    writeln!(asm_file, "\tcseal c11, c11, c2")?;
    writeln!(asm_file, "\tskip_seal:")?;
    writeln!(asm_file, "\tcgettag x6, c11")?;
    writeln!(asm_file, "\tbeq x6, zero, bad_test")?;
    writeln!(asm_file, "\tbne x11, x5, bad_test")?;
    writeln!(asm_file, "\tcgethigh x5, c5")?;
    writeln!(asm_file, "\tcgethigh x6, c11")?;
    writeln!(asm_file, "\tbne x6, x5, bad_test")?;
    writeln!(asm_file, "\tcsc c11, 0(c4)")?;
    writeln!(asm_file, "\tcincoffset c3, c3, 4")?;
    writeln!(asm_file, "\tj tag_init_loop")?;
    writeln!(asm_file, "tag_init_end:")?;

    writeln!(asm_file, "\t/* Write load filter bitmap entries (if any) */")?;
    for (start, (name, maybe_length)) in sections.iter() {
        // TODO: parametrise the start address
        // See also the linker code below
        if *start >= 0x30000000_u64 {
            if let Some(length) = maybe_length {
                writeln!(asm_file, "\tcla_abs 3, c1, {}", name)?;
                writeln!(asm_file, "\tcla_abs 4, c1, {}", start)?;
                writeln!(asm_file, "\tcincoffset c7, c3, {}", length)?;
                writeln!(asm_file, "write_loop_{}:", name)?;
                writeln!(asm_file, "\tclb x6, 0(c3)")?;
                writeln!(asm_file, "\tcsb x6, 0(c4)")?;
                writeln!(asm_file, "\tcincoffset c3, c3, 1")?;
                writeln!(asm_file, "\tcincoffset c4, c4, 1")?;
                writeln!(asm_file, "\tbne x3, x7, write_loop_{}", name)?;
            }
        }
    }

    writeln!(asm_file, "\t/* Set up exception handler */")?;
    writeln!(asm_file, "\tcspecialr c11, mtcc")?;
    writeln!(asm_file, "\tlui x3, %hi(finish)")?;
    writeln!(asm_file, "\taddi x3, x3, %lo(finish)")?;
    writeln!(asm_file, "\tcsetaddr c11, c11, x3")?;
    writeln!(asm_file, "\tcspecialw mtcc, c11")?;

    // Make sure the register we use for the initial cjr isn't c1 (aka cra), which has
    // different restrictions, and that we use something else for the max cap reg, because
    // the cla_abs macro can't use the same reg twice.
    let (jump_reg, max_reg) = if entry_reg == 1 { (exit_reg, entry_reg) } else { (entry_reg, exit_reg) };

    writeln!(asm_file, "\t/* Write general purpose registers */")?;
    writeln!(asm_file, "\tcmove c{}, c1", max_reg)?;
    writeln!(asm_file, "\tcla_abs {}, c{}, initial_cap_values", jump_reg, max_reg)?;
    for (i, (reg, _value)) in gprs.iter().enumerate() {
        writeln!(asm_file, "\tclc c{}, {}(c{})", *reg, 8*i as u32, jump_reg)?;
    }

    for (reg, value) in &system_registers {
        //TODO
    }
    writeln!(asm_file, "\t/* Start test */")?;
    writeln!(asm_file, "\tcla_abs {}, c{}, initial_PCC_value", jump_reg, max_reg)?;
    writeln!(asm_file, "\tclc c{0}, 0(c{0})", jump_reg)?;
    writeln!(asm_file, "\tcjr c{}", jump_reg)?;
    
    // ------

    // The bottom two bits of finish's location need to be zero because they're used to indicate
    // the mode in MTCC, rather than part of the address.
    writeln!(asm_file, "")?;
    writeln!(asm_file, ".align 2")?;
    writeln!(asm_file, "finish:")?;

    writeln!(asm_file, "\t/* Check registers */")?;
    writeln!(asm_file, "\tcspecialr c{}, mtdc", exit_reg)?;
    writeln!(asm_file, "\tcla_abs {}, c{}, final_cap_values", entry_reg, exit_reg)?;
    for (i, (reg, _value)) in post_gprs.iter().enumerate() {
        writeln!(asm_file, "clc c{}, {}(c{})", exit_reg, 8*i as u32, entry_reg)?;
        writeln!(asm_file, "csetequalexact x{0}, c{0}, c{1}", exit_reg, *reg)?;
        writeln!(asm_file, "\tbeq x{}, zero, comparison_fail", exit_reg)?;
    }
    // TODO: anything other than PCC
    writeln!(asm_file, "\t/* Check system registers */")?;
    writeln!(asm_file, "\tcspecialr c1, mtdc")?;
    writeln!(asm_file, "\tcla_abs 2, c1, final_PCC_value")?;
    writeln!(asm_file, "\tclc c2, 0(c2)")?;
    writeln!(asm_file, "\tcspecialr c3, MEPCC")?;
    writeln!(asm_file, "\tcsetequalexact x4, c2, c3")?;
    writeln!(asm_file, "\tbeq x4, zero, comparison_fail")?;

    writeln!(asm_file, "\t/* Check memory */")?;
    let mut name = 0;
    for (region, _contents) in pre_post_states.post_memory.iter() {
        writeln!(asm_file, "\tcla_abs 2, c1, {:#06x}", region.start)?;
        writeln!(asm_file, "\tcla_abs 3, c1, check_data{}", name)?;
        writeln!(asm_file, "\tlui x4, %hi({:#06x})", region.end)?;
        writeln!(asm_file, "\taddi x4, x4, %lo({:#06x})", region.end)?;
        writeln!(asm_file, "check_data_loop{}:", name)?;
        writeln!(asm_file, "\tclb x5, 0(c2)")?;
        writeln!(asm_file, "\tclb x6, 0(c3)")?;
        writeln!(asm_file, "\tbne x5, x6, comparison_fail")?;
        writeln!(asm_file, "\tcincoffset c2, c2, 1")?;
        writeln!(asm_file, "\tcincoffset c3, c3, 1")?;
        writeln!(asm_file, "\tbne x2, x4, check_data_loop{}", name)?;
        name += 1;
    }

    writeln!(asm_file, "\t/* Clear load filter before checking tags */")?;
    // TODO: parametrise
    writeln!(asm_file, "\tcla_abs 2, c1, 0x30000000")?;
    writeln!(asm_file, "\tli x3, 0x30000800")?;
    writeln!(asm_file, "filter_clear_loop:")?;
    writeln!(asm_file, "\tcsw zero, 0(c2)")?;
    writeln!(asm_file, "\tcincoffset c2, c2, 4")?;
    writeln!(asm_file, "\tbne x2, x3, filter_clear_loop")?;
    writeln!(asm_file, "")?;

    writeln!(asm_file, "\tcla_abs 2, c1, final_tag_set_locations")?;
    writeln!(asm_file, "check_set_tags_loop:")?;
    writeln!(asm_file, "\tclw x3, 0(c2)")?;
    writeln!(asm_file, "\tbeq x3, zero, check_set_tags_end")?;
    writeln!(asm_file, "\tcsetaddr c3, c1, x3")?;
    writeln!(asm_file, "\tclc c3, 0(c3)")?;
    writeln!(asm_file, "\tcgettag x3, c3")?;
    writeln!(asm_file, "\tbeq x3, zero, comparison_fail")?;
    writeln!(asm_file, "\tcincoffset c2, c2, 4")?;
    writeln!(asm_file, "\tj check_set_tags_loop")?;
    writeln!(asm_file, "check_set_tags_end:")?;
        
    writeln!(asm_file, "\tcla_abs 2, c1, final_tag_unset_locations")?;
    writeln!(asm_file, "check_unset_tags_loop:")?;
    writeln!(asm_file, "\tclw x3, 0(c2)")?;
    writeln!(asm_file, "\tbeq x3, zero, check_unset_tags_end")?;
    writeln!(asm_file, "\tcsetaddr c3, c1, x3")?;
    writeln!(asm_file, "\tclc c3, 0(c3)")?;
    writeln!(asm_file, "\tcgettag x3, c3")?;
    writeln!(asm_file, "\tbne x3, zero, comparison_fail")?;
    writeln!(asm_file, "\tcincoffset c2, c2, 4")?;
    writeln!(asm_file, "\tj check_unset_tags_loop")?;
    writeln!(asm_file, "check_unset_tags_end:")?;

    writeln!(asm_file, "\t/* Done print message */")?;
    writeln!(asm_file, "\tcspecialr c1, mtdc")?;
    writeln!(asm_file, "\tcla_abs 2, c1, ok_message")?;
    writeln!(asm_file, "\tj write_result")?;
    writeln!(asm_file, "\t.global bad_test")?;
    writeln!(asm_file, "bad_test:")?;
    writeln!(asm_file, "\tcspecialr c1, mtdc")?;
    writeln!(asm_file, "\tcla_abs 2, c1, bad_message")?;
    writeln!(asm_file, "\tj write_result")?;
    writeln!(asm_file, "\t.global comparison_fail")?;
    writeln!(asm_file, "comparison_fail:")?;
    writeln!(asm_file, "\tcspecialr c1, mtdc")?;
    writeln!(asm_file, "\tcla_abs 2, c1, fail_message")?;
    writeln!(asm_file, "write_result:")?;
    writeln!(asm_file, "\t/* Writes message to uart */")?;
    writeln!(asm_file, "\tcla_abs 3, c1, uart")?;
    writeln!(asm_file, "\tli x4, 0x05e5f0003")?;
    writeln!(asm_file, "\tcsw x4, 0x10(c3)")?;
    writeln!(asm_file, "\tli x4, 0x00000003")?;
    writeln!(asm_file, "\tcsw x4, 0x20(c3)")?; 
    writeln!(asm_file, "write_result_loop:")?;
    writeln!(asm_file, "\tclb x4, 0(c2)")?;
    writeln!(asm_file, "\tbeq x4, zero, haltsim")?;
    writeln!(asm_file, "\tcsw x4, 0x1c(c3)")?;
    writeln!(asm_file, "\tcincoffset c2, c2, 1")?;
    writeln!(asm_file, "\tj write_result_loop")?;

    writeln!(asm_file, "haltsim:")?;
    writeln!(asm_file, "\tli x4, 0x80")?;
    writeln!(asm_file, "\t#csb x4, 0(c3)")?;
    writeln!(asm_file, "loop_forever:")?;
    writeln!(asm_file, "\tj loop_forever")?;

    writeln!(asm_file, "ok_message:")?;
    writeln!(asm_file, "\t.ascii \"OK\\n\\000\"")?;
    writeln!(asm_file, "bad_message:")?;
    writeln!(asm_file, "\t.ascii \"BAD TEST\\n\\000\"")?;
    writeln!(asm_file, "fail_message:")?;
    writeln!(asm_file, "\t.ascii \"FAILED\\n\\000\"")?;

    let mut ld_file = File::create(&format!("{}.ld", base_name))?;
    writeln!(ld_file, "SECTIONS {{")?;

    for (vma, (name, _len)) in &sections {
        // The load filter bitmap is much higher than the rest of the test, write it
        // out alongside then move it using code above.
        if *vma < 0x3000_0000_u64 {
            writeln!(ld_file, "{0} {1:#018x} : {{ *({0}) }}", name, vma)?;
        } else {
            // Load filter
            writeln!(ld_file, "{0} : {{ *({0}) }}", name)?;
        }
    }

    writeln!(ld_file, "}}")?;
    writeln!(ld_file, "ENTRY(preamble)")?;
    writeln!(ld_file, "uart = {:#010x};", uart)?;
    // We don't use htif, but cheriot_sim gets upset if you don't say where it is
    writeln!(ld_file, "tohost = 0x80001000;")?;

    Ok(())
}

pub fn build_elf_file<B>(isa: &ISAConfig<B>, base_name: &str) -> Result<(), BuildError> {
    let assembler_result = isa
        .assembler
        .command()
        .args(&["-o", &format!("{}.o", base_name), &format!("{}.s", base_name)])
        .status()
        .map_err(|err| BuildError(format!("Failed to run assembler: {}", err)))?;

    if !assembler_result.success() {
        return Err(BuildError(format!("Assembler returned bad result code: {}", assembler_result)));
    }

    let linker_result = isa
        .linker
        .command()
        .args(&[
            "-o",
            &format!("{}.elf", base_name),
            "-T",
            &format!("{}.ld", base_name),
            "-n",
            &format!("{}.o", base_name),
        ])
        .status()
        .map_err(|err| BuildError(format!("Failed to run linker: {}", err)))?;

    if !linker_result.success() {
        return Err(BuildError(format!("Linker returned bad result code: {}", linker_result)));
    }

    Ok(())
}
