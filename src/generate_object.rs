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

use crate::extract_state::{GVAccessor, GroundVal, PrePostStates};
use crate::target::Target;

use isla_lib::concrete::BV;
use isla_lib::config::ISAConfig;
use isla_lib::zencode;

use std::collections::HashMap;
use std::convert::TryFrom;
use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::Write;
use std::path::Path;

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
    for line in bytes.chunks(16) {
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
    Ok(())
}

struct Flags {
    pre_nzcv: u32,
    post_nzcv_mask: u32,
    post_nzcv_value: u32,
}

fn get_nzcv<B: BV>(state: &HashMap<(&str, Vec<GVAccessor<&str>>), GroundVal<B>>) -> (u32, u32) {
    let mut mask = 0u32;
    let mut value = 0u32;
    for (flag, bit) in &[("zN", 8), ("zZ", 4), ("zC", 2), ("zV", 1)] {
        match state.get(&("zPSTATE", vec![GVAccessor::Field(flag)])) {
            Some(GroundVal::Bits(v)) => {
                mask |= bit;
                if !v.is_zero() {
                    value |= bit;
                }
            }
            Some(_) => panic!("PSTATE flag {} isn't a bitvector", flag),
            None => (),
        }
    }
    (mask, value)
}

fn get_flags<B: BV>(pre_post_states: &PrePostStates<B>) -> Flags {
    let (_, pre_nzcv) = get_nzcv(&pre_post_states.pre_registers);
    let (post_nzcv_mask, post_nzcv_value) = get_nzcv(&pre_post_states.post_registers);
    Flags { pre_nzcv, post_nzcv_mask, post_nzcv_value }
}

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
                Some(GroundVal::Bits(bs)) => Some((i, *bs)),
                Some(v) => panic!("Register {} was expected to be a bitvector, found {}", name, v),
                None => None,
            }
        })
        .collect()
}

fn get_vector_registers<B: BV>(state: &HashMap<(&str, Vec<GVAccessor<&str>>), GroundVal<B>>) -> Vec<(usize, B)> {
    (0..32)
        .filter_map(|i| {
            let name = "z_V";
            match state.get(&(name, vec![GVAccessor::Element(i)])) {
                Some(GroundVal::Bits(bs)) => Some((i, *bs)),
                Some(v) => panic!("Vector register {}.{} was expected to be a bitvector, found {}", name, i, v),
                None => None,
            }
        })
        .collect()
}

fn get_system_registers<B: BV, T: Target>(
    _target: T,
    state: &HashMap<(&str, Vec<GVAccessor<&str>>), GroundVal<B>>,
) -> Vec<(String, B)> {
    T::regs()
        .iter()
        .filter_map(|(reg, acc)| {
            let zreg = zencode::encode(reg);
            if acc.is_empty() && T::is_gpr(&zreg).is_none() && reg != "_PC" {
                match state.get(&(&zreg, vec![])) {
                    Some(GroundVal::Bits(bs)) => Some((reg.clone(), *bs)),
                    Some(v) => panic!("System register {} was expected to be a bitvector, found {}", reg, v),
                    None => None,
                }
            } else {
                None
            }
        })
        .collect()
}

pub fn make_asm_files<B: BV, T: Target>(
    target: T,
    base_name: String,
    pre_post_states: PrePostStates<B>,
    entry_reg: u32,
    exit_reg: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    let flags = get_flags(&pre_post_states);
    let mut asm_file = File::create(Path::new(&(base_name.clone() + ".s"))).expect("Unable to create .s file");
    let mut ld_file = File::create(Path::new(&(base_name + ".ld"))).expect("Unable to create .ld file");

    writeln!(ld_file, "SECTIONS {{")?;

    let mut name = 0;
    for (region, contents) in pre_post_states.pre_memory.iter() {
        writeln!(ld_file, ".data{0} {1:#010x} : {{ *(data{0}) }}", name, region.start)?;
        writeln!(asm_file, ".section data{}, #alloc, #write", name)?;
        write_bytes(&mut asm_file, contents)?;
        name += 1;
    }
    writeln!(ld_file, ".data {:#010x} : {{ *(data) }}", 0x00100000u64)?; /* TODO: parametrise */
    name = 0;
    for (_region, contents) in pre_post_states.post_memory.iter() {
        writeln!(asm_file, ".data")?;
        writeln!(asm_file, "check_data{}:", name)?;
        write_bytes(&mut asm_file, contents)?;
        name += 1;
    }

    name = 0;
    for (region, contents) in pre_post_states.code.iter() {
        writeln!(ld_file, ".text{0} {1:#010x} : {{ *(text{0}) }}", name, region.start)?;
        writeln!(asm_file, ".section text{}, #alloc, #execinstr", name)?;
        if name == 0 {
            writeln!(asm_file, "test_start:")?;
        }
        for word in contents.chunks(4) {
            writeln!(asm_file, "\t.inst {:#010x}", u32::from_le_bytes(TryFrom::try_from(word)?))?;
        }
        name += 1;
    }

    writeln!(ld_file, ".text  0x10300000 : {{ *(.text) }}")?;
    writeln!(ld_file, "}}")?;
    writeln!(ld_file, "ENTRY(preamble)")?;
    writeln!(ld_file, "trickbox = 0x13000000;")?;

    writeln!(asm_file, ".text")?;
    writeln!(asm_file, ".global preamble")?;
    writeln!(asm_file, "preamble:")?;
    for (reg, value) in get_numbered_registers(T::gpr_prefix(), T::gpr_pad(), 32, &pre_post_states.pre_registers) {
        writeln!(asm_file, "\tldr x{}, ={:#x}", reg, value.lower_u64())?;
    }
    let vector_registers = get_vector_registers(&pre_post_states.pre_registers);
    if !vector_registers.is_empty() {
        writeln!(asm_file, "\t/* Vector registers */")?;
        writeln!(asm_file, "\tmrs x{}, cptr_el3", entry_reg)?;
        writeln!(asm_file, "\tbfc x{}, #10, #1", entry_reg)?;
        writeln!(asm_file, "\tmsr cptr_el3, x{}", entry_reg)?;
        for (reg, value) in vector_registers {
            writeln!(asm_file, "\tldr q{}, =0x{:#x}", reg, value)?;
        }
    }
    writeln!(asm_file, "\tmov x{}, #{:#010x}", entry_reg, flags.pre_nzcv << 28)?;
    writeln!(asm_file, "\tmsr nzcv, x{}", entry_reg)?;
    for (reg, value) in get_system_registers(target, &pre_post_states.pre_registers) {
        writeln!(asm_file, "\tldr x{}, ={:#x}", entry_reg, value.lower_u64())?;
        writeln!(asm_file, "\tmsr {}, x{}", reg, entry_reg)?;
    }
    writeln!(asm_file, "\tldr x{}, =test_start", entry_reg)?;
    writeln!(asm_file, "\tldr x{}, =finish", exit_reg)?;
    writeln!(asm_file, "\tbr x{}", entry_reg)?;

    writeln!(asm_file, "finish:")?;
    /* Check the processor flags before they're trashed */
    if flags.post_nzcv_mask == 0 {
        writeln!(asm_file, "\t/* No processor flags to check */")?;
    } else {
        writeln!(asm_file, "\t/* Check processor flags */")?;
        writeln!(asm_file, "\tmrs x{}, nzcv", entry_reg)?;
        writeln!(asm_file, "\tubfx x{0}, x{0}, #28, #4", entry_reg)?;
        writeln!(asm_file, "\tmov x{}, #{:#03x}", exit_reg, flags.post_nzcv_mask)?;
        writeln!(asm_file, "\tand x{0}, x{0}, x{1}", entry_reg, exit_reg)?;
        writeln!(asm_file, "\tcmp x{}, #{:#03x}", entry_reg, flags.post_nzcv_value)?;
        writeln!(asm_file, "\tb.ne comparison_fail")?;
    }
    writeln!(asm_file, "\t/* Check registers */")?;
    for (reg, value) in get_numbered_registers(T::gpr_prefix(), T::gpr_pad(), 32, &pre_post_states.post_registers) {
        writeln!(asm_file, "\tldr x{}, ={:#x}", entry_reg, value.lower_u64())?;
        writeln!(asm_file, "\tcmp x{}, x{}", entry_reg, reg)?;
        writeln!(asm_file, "\tb.ne comparison_fail")?;
    }
    for (reg, value) in get_vector_registers(&pre_post_states.post_registers) {
        writeln!(asm_file, "\tldr x{}, ={:#x}", entry_reg, value.lower_u64())?;
        writeln!(asm_file, "\tmov x{}, v{}.d[0]", exit_reg, reg)?;
        writeln!(asm_file, "\tcmp x{}, x{}", entry_reg, exit_reg)?;
        writeln!(asm_file, "\tb.ne comparison_fail")?;
        writeln!(asm_file, "\tldr x{}, ={:#x}", entry_reg, value.shiftr(64).lower_u64())?;
        writeln!(asm_file, "\tmov x{}, v{}.d[1]", exit_reg, reg)?;
        writeln!(asm_file, "\tcmp x{}, x{}", entry_reg, exit_reg)?;
        writeln!(asm_file, "\tb.ne comparison_fail")?;
    }
    writeln!(asm_file, "\t/* Check memory */")?;
    let mut name = 0;
    for (region, _contents) in pre_post_states.post_memory.iter() {
        writeln!(asm_file, "\tldr x0, ={:#010x}", region.start)?;
        writeln!(asm_file, "\tldr x1, =check_data{}", name)?;
        writeln!(asm_file, "\tldr x2, ={:#010x}", region.end)?;
        writeln!(asm_file, "check_data_loop{}:", name)?;
        writeln!(asm_file, "\tldrb w3, [x0], #1")?;
        writeln!(asm_file, "\tldrb w4, [x1], #1")?;
        writeln!(asm_file, "\tcmp x3, x4")?;
        writeln!(asm_file, "\tb.ne comparison_fail")?;
        writeln!(asm_file, "\tcmp x0, x2")?;
        writeln!(asm_file, "\tb.ne check_data_loop{}", name)?;
        name += 1;
    }
    writeln!(asm_file, "\t/* Done, print message */")?;
    writeln!(asm_file, "\tldr x0, =ok_message")?;
    writeln!(asm_file, "\tb write_tube")?;
    writeln!(asm_file, "comparison_fail:")?;
    writeln!(asm_file, "\tldr x0, =fail_message")?;
    writeln!(asm_file, "write_tube:")?;
    writeln!(asm_file, "\tldr x1, =trickbox")?;
    writeln!(asm_file, "write_tube_loop:")?;
    writeln!(asm_file, "\tldrb w2, [x0], #1")?;
    writeln!(asm_file, "\tstrb w2, [x1]")?;
    writeln!(asm_file, "\tb write_tube_loop")?;

    writeln!(asm_file, "ok_message:")?;
    writeln!(asm_file, "\t.ascii \"OK\\n\\004\"")?;
    writeln!(asm_file, "fail_message:")?;
    writeln!(asm_file, "\t.ascii \"FAILED\\n\\004\"")?;

    Ok(())
}

pub fn build_elf_file<B>(isa: &ISAConfig<B>, base_name: String) {
    let assembler_result = isa
        .assembler
        .command()
        .args(&["-march=armv8.2-a", "-o", &(base_name.clone() + ".o"), &(base_name.clone() + ".s")])
        .status()
        .expect("Failed to run assembler");

    if !assembler_result.success() {
        panic!("Assembler returned bad result code: {}", assembler_result);
    }

    let linker_result = isa
        .linker
        .command()
        .args(&["-o", &(base_name.clone() + ".elf"), "-T", &(base_name.clone() + ".ld"), "-n", &(base_name + ".o")])
        .status()
        .expect("Failed to run linker");

    if !linker_result.success() {
        panic!("Linker returned bad result code: {}", linker_result);
    }
}
