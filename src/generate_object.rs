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

// Avoid a dependency on a Morello assembler by encoding these instructions directly.
// Note that for xn to refer to a normal register read we must be in A64 mode
fn write_ldr_off(asm_file: &mut File, ct: u32, xn: u32, imm: u32) -> Result<(), Box<dyn std::error::Error>> {
    let v: u32 = 0xc2400000 | imm << 10 | xn << 5 | ct;
    writeln!(asm_file, "\t.inst {:#010x} // ldr c{}, [x{}, #{}]", v, ct, xn, imm)?;
    Ok(())
}

fn write_ldr_off_int(asm_file: &mut File, xt: u32, cn: u32, imm: u32) -> Result<(), Box<dyn std::error::Error>> {
    let v: u32 = 0x82600c00 | imm << 12 | cn << 5 | xt;
    writeln!(asm_file, "\t.inst {:#010x} // ldr x{}, [c{}, #{}]", v, xt, cn, imm)?;
    Ok(())
}

fn write_str_off_int(asm_file: &mut File, xt: u32, cn: u32, imm: u32) -> Result<(), Box<dyn std::error::Error>> {
    let v: u32 = 0x82400c00 | imm << 12 | cn << 5 | xt;
    writeln!(asm_file, "\t.inst {:#010x} // str x{}, [c{}, #{}]", v, xt, cn, imm)?;
    Ok(())
}

fn write_aldr_off(asm_file: &mut File, ct: u32, cn: u32, imm: u32) -> Result<(), Box<dyn std::error::Error>> {
    let v: u32 = 0x82600000 | imm << 12 | cn << 5 | ct;
    writeln!(asm_file, "\t.inst {:#010x} // ldr c{}, [c{}, #{}]", v, ct, cn, imm)?;
    Ok(())
}

fn write_chktgd(asm_file: &mut File, cn: u32) -> Result<(), Box<dyn std::error::Error>> {
    let v: u32 = 0xc2c23001 | cn << 5;
    writeln!(asm_file, "\t.inst {:#010x} // chktgd c{}", v, cn)?;
    Ok(())
}

fn write_sctag(asm_file: &mut File, cd: u32, cn: u32, xm: u32) -> Result<(), Box<dyn std::error::Error>> {
    let v: u32 = 0xc2c08000 | xm << 16 | cn << 5 | cd;
    writeln!(asm_file, "\t.inst {:#010x} // sctag c{}, c{}, c{}", v, cd, cn, xm)?;
    Ok(())
}

fn write_str_off(asm_file: &mut File, ct: u32, xn: u32, imm: u32) -> Result<(), Box<dyn std::error::Error>> {
    let v: u32 = 0xc2000000 | imm << 10 | xn << 5 | ct;
    writeln!(asm_file, "\t.inst {:#010x} // str c{}, [x{}, #{}]", v, ct, xn, imm)?;
    Ok(())
}

fn write_cpy(asm_file: &mut File, cd: u32, cn: u32) -> Result<(), Box<dyn std::error::Error>> {
    let v: u32 = 0xc2c1d000 | cn << 5 | cd;
    writeln!(asm_file, "\t.inst {:#010x} // cpy c{}, c{}", v, cd, cn)?;
    Ok(())
}

fn write_br(asm_file: &mut File, cn: u32) -> Result<(), Box<dyn std::error::Error>> {
    let v: u32 = 0b11_0000101100_00100_0_0_100_00000_0_0_0_00 | cn << 5;
    writeln!(asm_file, "\t.inst {:#010x} // br c{}", v, cn)?;
    Ok(())
}

fn write_cvtp(asm_file: &mut File, cd: u32, rn: u32) -> Result<(), Box<dyn std::error::Error>> {
    let v: u32 = 0b11000010110001011_0_1_100_00000_00000 | rn << 5 | cd;
    writeln!(asm_file, "\t.inst {:#010x} // cvtp c{}, x{}", v, cd, rn)?;
    Ok(())
}

fn write_scvalue(asm_file: &mut File, cd: u32, cn: u32, rm: u32) -> Result<(), Box<dyn std::error::Error>> {
    let v: u32 = 0b11000010110_00000_0_1_0_000_00000_00000 | rm << 16 | cn << 5 | cd;
    writeln!(asm_file, "\t.inst {:#010x} // scvalue c{}, c{}, x{}", v, cd, cn, rm)?;
    Ok(())
}

fn write_add_imm(asm_file: &mut File, cd: u32, cn: u32, imm12: u32) -> Result<(), Box<dyn std::error::Error>> {
    let v: u32 = 0b00000010_0_0_000000000000_00000_00000 | imm12 << 10 | cn << 5 | cd;
    writeln!(asm_file, "\t.inst {:#010x} // add c{}, c{}, #{}", v, cd, cn, imm12)?;
    Ok(())
}

type SystemRegister = (&'static str, u32, u32, u32, u32, u32);

fn write_msr_cap(asm_file: &mut File, (reg, op0, op1, crn, crm, op2): &SystemRegister, ct: u32) -> Result<(), Box<dyn std::error::Error>> {
    let o0 = match op0 {
        2 => 0,
        3 => 1,
        _ => panic!("Bad op0 for MSR: {}", op0),
    };
    let v: u32 = 0b11000010100_0_0_000_0000_0000_000_00000 | o0 << 19 | op1 << 16 | crn << 12 | crm << 8 | op2 << 5 | ct;
    writeln!(asm_file, "\t.inst {:#010x} // msr {}, c{}", v, reg, ct)?;
    Ok(())
}

fn write_mrs_cap(asm_file: &mut File, ct: u32, (reg, op0, op1, crn, crm, op2): &SystemRegister) -> Result<(), Box<dyn std::error::Error>> {
    let o0 = match op0 {
        2 => 0,
        3 => 1,
        _ => panic!("Bad op0 for MRS: {}", op0),
    };
    let v: u32 = 0b11000010100_1_0_000_0000_0000_000_00000 | o0 << 19 | op1 << 16 | crn << 12 | crm << 8 | op2 << 5 | ct;
    writeln!(asm_file, "\t.inst {:#010x} // mrs c{}, {}", v, ct, reg)?;
    Ok(())
}

const REG_CVBAR_EL3: SystemRegister = ("CVBAR_EL3", 0b11, 0b110, 0b1100, 0b0000, 0b000);
const REG_CVBAR_EL1: SystemRegister = ("CVBAR_EL1", 0b11, 0b000, 0b1100, 0b0000, 0b000);
const REG_CELR_EL1 : SystemRegister = ("CELR_EL1",  0b11, 0b000, 0b0100, 0b0000, 0b001);
const REG_CELR_EL2 : SystemRegister = ("CELR_EL2",  0b11, 0b100, 0b0100, 0b0000, 0b001);
const REG_CELR_EL3 : SystemRegister = ("CELR_EL3",  0b11, 0b110, 0b0100, 0b0000, 0b001);
const REG_DDC_EL0  : SystemRegister = ("DDC_EL0",   0b11, 0b000, 0b0100, 0b0001, 0b001);
const REG_DDC_EL1  : SystemRegister = ("DDC_EL1",   0b11, 0b100, 0b0100, 0b0001, 0b001);
const REG_DDC_EL2  : SystemRegister = ("DDC_EL2",   0b11, 0b110, 0b0100, 0b0001, 0b001);
const REG_DDC_EL3  : SystemRegister = ("DDC_EL3",   0b11, 0b011, 0b0100, 0b0001, 0b001);
const REG_RDDC_EL0 : SystemRegister = ("RDDC_EL0",  0b11, 0b011, 0b0100, 0b0011, 0b001);
const REG_RCSP_EL0 : SystemRegister = ("RSP_EL0",   0b11, 0b111, 0b0100, 0b0001, 0b011);
const REG_CSP_EL0  : SystemRegister = ("CSP_EL0",   0b11, 0b000, 0b0100, 0b0001, 0b000);
const REG_CSP_EL1  : SystemRegister = ("CSP_EL1",   0b11, 0b100, 0b0100, 0b0001, 0b000);
const REG_CSP_EL2  : SystemRegister = ("CSP_EL2",   0b11, 0b110, 0b0100, 0b0001, 0b000);

fn write_chkeq(asm_file: &mut File, cn: u32, cm: u32) -> Result<(), Box<dyn std::error::Error>> {
    let v: u32 = 0b11_000010110_00000_1_0_1_001_00000_0_0_0_01 | cm << 16 | cn << 5;
    writeln!(asm_file, "\t.inst {:#010x} // chkeq c{}, c{}", v, cn, cm)?;
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
    _target: &T,
    regs: &[(String, Vec<GVAccessor<String>>)],
    state: &HashMap<(&str, Vec<GVAccessor<&str>>), GroundVal<B>>,
) -> Vec<(String, B)> {
    regs
        .iter()
        .filter_map(|(reg, acc)| {
            let zreg = zencode::encode(reg);
            if acc.is_empty() && T::is_gpr(&zreg).is_none() && reg != "_PC" {
                match state.get(&(&zreg, vec![])) {
                    Some(GroundVal::Bits(bs)) => Some((reg.clone(), *bs)),
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
    if let Some(GroundVal::Bits(final_pc)) = pre_post_states.post_registers.get(&("z_PC", vec![])) {
        final_pc.lower_u64() + 4
    } else {
        panic!("Missing PC register in post state");
    }
}

fn write_cap_esr_check(
    asm_file: &mut File,
    val: u64,
    scratch_1: u32,
    scratch_2: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    let ec = (val & 0x0000_0000_fc00_0000) >> 26;
    writeln!(asm_file, "\tldr x{}, =esr_el1_dump_address", scratch_1)?;
    writeln!(asm_file, "\tldr x{}, [x{}]", scratch_1, scratch_1)?;
    let mask: u64 =
    // Atomics with bad bounds and no store permissions might fault
    // with a bounds fault (e.g., in the ASL) or a permission fault
    // (in the fast model), cope with either.
        if (ec == 0b100100 || ec == 0b100101) && val & 0b111111 == 0b101010 && val & 1 << 6 == 0 { 0b11000001 }
    else {
        match ec {
            // If we pretend during symbol execution that there's no address
            // translation then ESR_EL1 may indicate the wrong translation
            // stage/level, so mask those out.
            0b100000 | 0b100001 | 0b100100 | 0b100101 =>
                if val & 0b100000 == 0 { 0b1000_0011 } else { 0b1000_0000 }, // S1PTW, bottom bits of IFSC / DFSC
            _ => 0
        }
    };
    if mask != 0 {
        writeln!(asm_file, "\tmov x{}, {:#x}", scratch_2, mask)?;
        writeln!(asm_file, "\torr x{}, x{}, x{}", scratch_1, scratch_1, scratch_2)?;
    }
    writeln!(asm_file, "\tldr x{}, ={:#x}", scratch_2, val | mask)?;
    writeln!(asm_file, "\tcmp x{}, x{}", scratch_2, scratch_1)?;
    writeln!(asm_file, "\tb.ne comparison_fail")?;
    Ok(())
}

pub fn write_main_memory<B: BV>(
    asm_file: &mut File,
    ld_file: &mut File,
    pre_post_states: &PrePostStates<B>,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut name = 0;
    for (region, contents) in pre_post_states.pre_memory.iter() {
        writeln!(ld_file, ".data{0} {1:#010x} : {{ *(data{0}) }}", name, region.start)?;
        writeln!(asm_file, ".section data{}, #alloc, #write", name)?;
        write_bytes(asm_file, contents)?;
        name += 1;
    }
    writeln!(ld_file, ".data {:#010x} : {{ *(data) }}", 0x00100000u64)?; /* TODO: parametrise */
    name = 0;
    for (_region, contents) in pre_post_states.post_memory.iter() {
        writeln!(asm_file, ".data")?;
        writeln!(asm_file, "check_data{}:", name)?;
        write_bytes(asm_file, contents)?;
        name += 1;
    }
    Ok(())
}

pub fn write_capability_data<B: BV, T: Target>(
    target: &T,
    asm_file: &mut File,
    gprs: &[(u32, B)],
    post_gprs: &[(u32, B)],
    system_registers: &[(String, B)],
    post_system_registers: &[(String, B)],
    pre_post_states: &PrePostStates<B>,
    system_cap_map: &HashMap<String, SystemRegister>,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut extra_tags = vec![];
    writeln!(asm_file, ".data")?;
    writeln!(asm_file, ".balign 16")?;
    writeln!(asm_file, "initial_cap_values:")?;
    for (i, (reg, value)) in gprs.iter().enumerate() {
        let value_except_tag = value.slice(0, 128).unwrap();
        writeln!(asm_file, "\t/* C{} */", reg)?;
        writeln!(asm_file, "\t.octa 0x{:#x}", value_except_tag)?;
        if !value.slice(128, 1).unwrap().is_zero() {
            extra_tags.push(format!("initial_cap_values + {}", i * 16));
        }
    }
    if target.run_in_el0() {
        // Location to restart test from after faulting to EL1
        writeln!(asm_file, "el1_vector_jump_cap:")?;
        writeln!(asm_file, "\t.dword 0x40400300")?;
        writeln!(asm_file, "\t.dword 0xFFFFC00000010005")?;
        extra_tags.push("el1_vector_jump_cap".to_string());
    }
    writeln!(asm_file, "final_cap_values:")?;
    for (i, (reg, value)) in post_gprs.iter().enumerate() {
        let value_except_tag = value.slice(0, 128).unwrap();
        writeln!(asm_file, "\t/* C{} */", reg)?;
        writeln!(asm_file, "\t.octa 0x{:#x}", value_except_tag)?;
        if !value.slice(128, 1).unwrap().is_zero() {
            extra_tags.push(format!("final_cap_values + {}", i * 16));
        }
    }
    for (reg, value) in system_registers {
        if reg == "VBAR_EL1" || reg == "SP_EL3" || system_cap_map.contains_key(reg) {
            let value =
                // The harness code provides its own vector table, overrides CCTLR_EL1.C64E, and
                // jumps to the intended destination if the test isn't over, so apply C64E here.
                if reg == "VBAR_EL1" {
                    let c64 = match system_registers.iter().find(|(reg, _value)| reg == "CCTLR_EL1") {
                        Some((_, value)) => ! (*value & B::new(1 << 5, 64)).is_zero(),
                        None => false,
                    };
                    if c64 { *value | B::new(1, 64) } else { *value }
                } else {
                    *value
                };
            let value_except_tag = value.slice(0, 128).unwrap();
            writeln!(asm_file, "initial_{}_value:", reg)?;
            writeln!(asm_file, "\t.octa 0x{:#x}", value_except_tag)?;
            if !value.slice(128, 1).unwrap().is_zero() {
                extra_tags.push(format!("initial_{}_value", reg));
            }
        }
    }
    for (reg, value) in post_system_registers {
        // PCC is checked using ELR_EL1
        let value = if reg == "PCC" {
            assert!(target.run_in_el0());
            value.add_i128(4)
        } else {
            *value
        };
        if reg == "SP_EL3" || reg == "PCC" || system_cap_map.contains_key(reg) {
            let value_except_tag = value.slice(0, 128).unwrap();
            writeln!(asm_file, "final_{}_value:", reg)?;
            writeln!(asm_file, "\t.octa 0x{:#x}", value_except_tag)?;
            if !value.slice(128, 1).unwrap().is_zero() {
                extra_tags.push(format!("final_{}_value", reg));
            }
        }
    }
    if let Some(GroundVal::Bits(value)) = pre_post_states.pre_registers.get(&("zPCC", vec![])) {
        let mut value_except_tag = value.slice(0, 128).unwrap();
        if let Some(GroundVal::Bits(bs)) = pre_post_states.pre_registers.get(&("zPSTATE", vec![GVAccessor::Field("zC64")])) {
            if !bs.is_zero() && !target.run_in_el0() {
                value_except_tag = value_except_tag.add_i128(1);
            }
        }
        writeln!(asm_file, "pcc_return_ddc_capabilities:")?;
        writeln!(asm_file, "\t.dword pcc_return_ddc_capabilities")?;
        writeln!(asm_file, "\t.dword 0xFFFFC00000010005")?;
        writeln!(asm_file, "\t.octa 0x{:#x}", value_except_tag)?;
        writeln!(asm_file, "\t.dword finish")?;
        writeln!(asm_file, "\t.dword 0xFFFFC00000010005")?;
        if let Some(GroundVal::Bits(value)) = pre_post_states.pre_registers.get(&("zDDC_EL3", vec![])) {
            let value_except_tag = value.slice(0, 128).unwrap();
            writeln!(asm_file, "\t.octa 0x{:#x}", value_except_tag)?;
            if !value.slice(128, 1).unwrap().is_zero() {
                extra_tags.push(String::from("pcc_return_ddc_capabilities + 48"));
            }
        }
    }
    
    writeln!(asm_file, ".balign 8")?;
    writeln!(asm_file, "initial_tag_locations:")?;
    writeln!(asm_file, "\t.dword pcc_return_ddc_capabilities")?;
    writeln!(asm_file, "\t.dword pcc_return_ddc_capabilities + 16")?;
    writeln!(asm_file, "\t.dword pcc_return_ddc_capabilities + 32")?;
    for (region, tags) in pre_post_states.pre_tag_memory.iter() {
        for (i, tag) in tags.iter().enumerate() {
            if *tag {
                writeln!(asm_file, "\t.dword {:#018x}", region.start + i as u64)?;
            }
        }
    }
    for address in extra_tags {
        writeln!(asm_file, "\t.dword {}", address)?;
    }
    writeln!(asm_file, "\t.dword 0")?;

    writeln!(asm_file, "final_tag_set_locations:")?;
    for (addr, tag) in pre_post_states.post_tag_memory.iter() {
        if *tag {
            writeln!(asm_file, "\t.dword {:#018x}", addr)?;
        }
    }
    writeln!(asm_file, "\t.dword 0")?;

    writeln!(asm_file, "final_tag_unset_locations:")?;
    for (addr, tag) in pre_post_states.post_tag_memory.iter() {
        if !*tag {
            writeln!(asm_file, "\t.dword {:#018x}", addr)?;
        }
    }
    writeln!(asm_file, "\t.dword 0")?;

    writeln!(asm_file, "esr_el1_dump_address:")?;
    writeln!(asm_file, "\t.dword 0")?;
    Ok(())
}

// Decide whether a fault to EL1 is the result of the SVC at the end of the test, or a midway through
// the test.  Avoids changing the NZCV flags.
fn write_el1_vector(
    asm_file: &mut File,
    scratch_reg_1: u32,
    scratch_reg_2: u32,
    exit_address: u64,
    table_offset: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    // Load via capabilities here to avoid using DDC.  We don't know what
    // CCTLR_EL3.PCCBO is set to, so use an scvalue to be sure we get
    // the right value

    // Stash ESR_EL1 in case we want to check it at the end, and also use it to
    // see if we've taken an exception before - we should only do at most one
    // during the test because otherwise it will loop.  Checking allows us to
    // easily bail out if we keep faulting.  Note that the initial value of 0 at
    // esr_el1_dump_address won't occur in practice because it's for a 16-bit
    // instruction.
    writeln!(asm_file, "\tldr x{}, =esr_el1_dump_address", scratch_reg_1)?;
    write_cvtp(asm_file, scratch_reg_2, scratch_reg_1)?;
    write_scvalue(asm_file, scratch_reg_2, scratch_reg_2, scratch_reg_1)?;
    write_ldr_off_int(asm_file, scratch_reg_1, scratch_reg_2, 0)?;
    writeln!(asm_file, "\tcbnz x{}, #28", scratch_reg_1)?;
    writeln!(asm_file, "\tmrs x{}, ESR_EL1", scratch_reg_1)?;
    write_str_off_int(asm_file, scratch_reg_1, scratch_reg_2, 0)?;
    writeln!(asm_file, "\tldr x{}, ={:#x}", scratch_reg_1, exit_address)?;
    writeln!(asm_file, "\tmrs x{}, ELR_EL1", scratch_reg_2)?;
    writeln!(asm_file, "\tsub x{}, x{}, x{}", scratch_reg_1, scratch_reg_1, scratch_reg_2)?;
    writeln!(asm_file, "\tcbnz x{}, #8", scratch_reg_1)?;
    writeln!(asm_file, "\tsmc 0")?;
    writeln!(asm_file, "\tldr x{}, =initial_VBAR_EL1_value", scratch_reg_1)?;
    write_cvtp(asm_file, scratch_reg_2, scratch_reg_1)?;
    write_scvalue(asm_file, scratch_reg_2, scratch_reg_2, scratch_reg_1)?;
    write_aldr_off(asm_file, scratch_reg_1, scratch_reg_2, 0)?;
    write_add_imm(asm_file, scratch_reg_1, scratch_reg_1, table_offset)?;
    write_br(asm_file, scratch_reg_1)?;
    Ok(())
}

pub fn make_asm_files<B: BV, T: Target>(
    target: &T,
    base_name: &str,
    instr_map: &HashMap<B, String>,
    pre_post_states: PrePostStates<B>,
    entry_reg: u32,
    exit_reg: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    let flags = get_flags(&pre_post_states);
    let mut asm_file = File::create(&format!("{}.s", base_name))?;
    let mut ld_file = File::create(&format!("{}.ld", base_name))?;

    let mut system_cap_map: HashMap<String, SystemRegister> = HashMap::new();
    system_cap_map.insert("ELR_EL1".to_string(), REG_CELR_EL1);
    system_cap_map.insert("ELR_EL2".to_string(), REG_CELR_EL2);
    system_cap_map.insert("ELR_EL3".to_string(), REG_CELR_EL3);
    system_cap_map.insert("RDDC_EL0".to_string(), REG_RDDC_EL0);
    system_cap_map.insert("DDC_EL0".to_string(), REG_DDC_EL0);
    system_cap_map.insert("DDC_EL1".to_string(), REG_DDC_EL1);
    system_cap_map.insert("DDC_EL2".to_string(), REG_DDC_EL2);
    // DDC_EL3 is treated as a special case
    system_cap_map.insert("RSP_EL0".to_string(), REG_RCSP_EL0);
    system_cap_map.insert("SP_EL0".to_string(), REG_CSP_EL0);
    system_cap_map.insert("SP_EL1".to_string(), REG_CSP_EL1);
    system_cap_map.insert("SP_EL2".to_string(), REG_CSP_EL2);

    writeln!(ld_file, "SECTIONS {{")?;

    let gprs = get_numbered_registers(T::gpr_prefix(), T::gpr_pad(), 32, &pre_post_states.pre_registers);
    let post_gprs = get_numbered_registers(T::gpr_prefix(), T::gpr_pad(), 32, &pre_post_states.post_registers);
    let system_registers = get_system_registers(target, &target.regs(), &pre_post_states.pre_registers);
    let post_system_registers = get_system_registers(target, &target.post_regs(), &pre_post_states.post_registers);

    let mut name = 0;
    for (region, contents) in pre_post_states.code.iter() {
        // The AT(...) version of the address allows the region to be executed in a second mapping that's non-writable, and
        // hence executable at EL1, while being loaded at the lower physcial address.
        writeln!(ld_file, ".text{0} {1:#010x} : AT({2:#010x}) {{ *(text{0}) }}", name, region.start, region.start & 0x3fff_ffff)?;
        writeln!(asm_file, ".section text{}, #alloc, #execinstr", name)?;
        if name == 0 {
            writeln!(asm_file, "test_start:")?;
        }
        let mut zeros = 0;
        for word in contents.chunks(4) {
            let word_u32 = u32::from_le_bytes(TryFrom::try_from(word)?);
            if word_u32 == 0 {
                zeros += 4;
            } else {
                if zeros > 0 { writeln!(asm_file, "\t.zero {}", zeros)?; };
                zeros = 0;
                write!(asm_file, "\t.inst {:#010x}", word_u32)?;
                if let Some(description) = instr_map.get(&B::new(word_u32 as u64, 32)) {
                    writeln!(asm_file, " // {}", description)?;
                } else {
                    writeln!(asm_file)?;
                }
            }
        }
        if zeros > 0 { writeln!(asm_file, "\t.zero {}", zeros)?; };
        name += 1;
    }

    writeln!(ld_file, ".text  0x10300000 : {{ *(.text) }}")?;

    writeln!(asm_file, ".text")?;
    writeln!(asm_file, ".global preamble")?;
    writeln!(asm_file, "preamble:")?;

    if target.has_capabilities() {
        writeln!(asm_file, "\t/* Ensure Morello is on */")?;
        writeln!(asm_file, "\tmov x0, 0x200")?;
        writeln!(asm_file, "\tmsr cptr_el3, x0")?;
        writeln!(asm_file, "\tisb")?;

        // We don't know what CCTLR_EL3.PCCBO is set to, so use an
        // scvalue to be sure we get the right value
        writeln!(asm_file, "\t/* Set exception handler */")?;
        writeln!(asm_file, "\tldr x0, =vector_table")?;
        write_cvtp(&mut asm_file, 1, 0)?;
        write_scvalue(&mut asm_file, 1, 1, 0)?;
        write_msr_cap(&mut asm_file, &REG_CVBAR_EL3, 1)?;
	if target.run_in_el0() {
            writeln!(asm_file, "\tldr x0, =vector_table_el1")?;
            write_cvtp(&mut asm_file, 1, 0)?;
            write_scvalue(&mut asm_file, 1, 1, 0)?;
            write_msr_cap(&mut asm_file, &REG_CVBAR_EL1, 1)?;
	}
        writeln!(asm_file, "\tisb")?;

        writeln!(asm_file, "\t/* Set up translation */")?;
        writeln!(asm_file, "\tldr x0, =tt_l1_base")?;
        writeln!(asm_file, "\tmsr ttbr0_el3, x0")?;
	if target.run_in_el0() {
            writeln!(asm_file, "\tmsr ttbr0_el1, x0")?;
	}
        writeln!(asm_file, "\tmov x0, #0xff")?;
        writeln!(asm_file, "\tmsr mair_el3, x0")?;
	if target.run_in_el0() {
            writeln!(asm_file, "\tmsr mair_el1, x0")?;
	}
        writeln!(asm_file, "\tldr x0, =0x0d003519")?;
        writeln!(asm_file, "\tmsr tcr_el3, x0")?;
	if target.run_in_el0() {
            writeln!(asm_file, "\tldr x0, =0x0000320000803519 // No cap effects, inner shareable, normal, outer write-back read-allocate write-allocate cacheable")?;
            writeln!(asm_file, "\tmsr tcr_el1, x0")?;
	}
        writeln!(asm_file, "\tisb")?;
        writeln!(asm_file, "\ttlbi alle3")?;
	if target.run_in_el0() {
            writeln!(asm_file, "\ttlbi alle1")?;
	}
        writeln!(asm_file, "\tdsb sy")?;
	writeln!(asm_file, "\tldr x0, =0x30851035")?;
	writeln!(asm_file, "\tmsr sctlr_el3, x0")?;
        writeln!(asm_file, "\tisb")?;

        writeln!(asm_file, "\t/* Write tags to memory */")?;
        writeln!(asm_file, "\tldr x0, =initial_tag_locations")?;
        writeln!(asm_file, "\tmov x1, #1")?;
        writeln!(asm_file, "tag_init_loop:")?;
        writeln!(asm_file, "\tldr x2, [x0], #8")?;
        writeln!(asm_file, "\tcbz x2, tag_init_end")?;
        write_ldr_off(&mut asm_file, 3, 2, 0)?;
        write_sctag(&mut asm_file, 3, 3, 1)?;
        write_str_off(&mut asm_file, 3, 2, 0)?;
        writeln!(asm_file, "\tb tag_init_loop")?;
        writeln!(asm_file, "tag_init_end:")?;

        writeln!(asm_file, "\t/* Write general purpose registers */")?;
        writeln!(asm_file, "\tldr x{}, =initial_cap_values", entry_reg)?;
        for (i, (reg, _value)) in gprs.iter().enumerate() {
            write_ldr_off(&mut asm_file, *reg, entry_reg, i as u32)?;
        }
    } else {
        writeln!(asm_file, "\tldr x0, =vector_table")?;
        writeln!(asm_file, "\tmsr vbar_el3, x0")?;
        writeln!(asm_file, "\tisb")?;

        writeln!(asm_file, "\t/* Write general purpose registers */")?;
        for (reg, value) in &gprs {
            writeln!(asm_file, "\tldr x{}, ={:#x}", *reg, value.lower_u64())?;
        }
    }

    let vector_registers = get_vector_registers(&pre_post_states.pre_registers);
    if !vector_registers.is_empty() {
        writeln!(asm_file, "\t/* Vector registers */")?;
        writeln!(asm_file, "\tmrs x{}, cptr_el3", entry_reg)?;
        writeln!(asm_file, "\tbfc x{}, #10, #1", entry_reg)?;
        writeln!(asm_file, "\tmsr cptr_el3, x{}", entry_reg)?;
        writeln!(asm_file, "\tisb")?;
        for (reg, value) in vector_registers {
            writeln!(asm_file, "\tldr q{}, =0x{:#x}", reg, value)?;
        }
    }

    writeln!(asm_file, "\t/* Set up flags and system registers */")?;
    if target.run_in_el0() {
	let c64: u64 =
	    if let Some(GroundVal::Bits(bs)) = pre_post_states.pre_registers.get(&("zPSTATE", vec![GVAccessor::Field("zC64")])) {
		if !bs.is_zero() { 1 << 26 } else { 0 }
	    } else {
		0
	    };
	writeln!(asm_file, "\tldr x{}, ={:#x}", entry_reg, (flags.pre_nzcv << 28) as u64 | c64)?;
	writeln!(asm_file, "\tmsr SPSR_EL3, x{}", entry_reg)?;
    } else {
	writeln!(asm_file, "\tmov x{}, #{:#010x}", entry_reg, flags.pre_nzcv << 28)?;
	writeln!(asm_file, "\tmsr nzcv, x{}", entry_reg)?;
    }
    for (reg, value) in &system_registers {
        if *reg == "SP_EL3" {
            if target.has_capabilities() {
                writeln!(asm_file, "\tldr x{}, =initial_SP_EL3_value", entry_reg)?;
                write_ldr_off(&mut asm_file, entry_reg, entry_reg, 0)?;
                write_cpy(&mut asm_file, 31, entry_reg)?;
            } else {
                writeln!(asm_file, "\tldr x{}, ={:#x}", entry_reg, value.lower_u64())?;
                writeln!(asm_file, "\tmov sp, x{}", entry_reg)?;
            }
        } else if let Some(operand) = system_cap_map.get(reg) {
            writeln!(asm_file, "\tldr x{}, =initial_{}_value", entry_reg, reg)?;
            write_ldr_off(&mut asm_file, entry_reg, entry_reg, 0)?;
            write_msr_cap(&mut asm_file, operand, entry_reg)?;
        } else if *reg != "DDC_EL3" && *reg != "PCC" && *reg != "VBAR_EL1" {
            let mut value = value.lower_u64();
            // Ensure MMU is on for Morello even if we didn't use it in symbolic execution
            if (reg == "SCTLR_EL3" || reg == "SCTLR_EL1") && target.has_capabilities() { value |= 0b1_0000_0000_0101; };
            // The harness exception handler needs to be run in A64, even if the test continues in C64
            if reg == "CCTLR_EL1" { value &= !(1 << 5) };
            writeln!(asm_file, "\tldr x{}, ={:#x}", entry_reg, value)?;
            // Avoid requirement for Morello assembler
            let (name, comment) =
                if *reg == "CCTLR_EL3" { ("S3_6_C1_C2_2", " // CCTLR_EL3") }
	        else if  *reg == "CCTLR_EL2" { ("S3_4_C1_C2_2", " // CCTLR_EL2") }
	        else if  *reg == "CCTLR_EL1" { ("S3_0_C1_C2_2", " // CCTLR_EL1") }
	        else if  *reg == "CCTLR_EL0" { ("S3_3_C1_C2_2", " // CCTLR_EL0") }
                else if  *reg == "CSCR_EL3"  { ("S3_6_C1_C2_3", " // CSCR_EL3")  }
	        else { (reg.as_str(), "") };
            writeln!(asm_file, "\tmsr {}, x{}{}", name, entry_reg, comment)?;
        }
    }
    writeln!(asm_file, "\tisb")?;

    writeln!(asm_file, "\t/* Start test */")?;
    if target.has_capabilities() {
        writeln!(asm_file, "\tldr x{}, =pcc_return_ddc_capabilities", exit_reg)?;
        write_ldr_off(&mut asm_file, exit_reg, exit_reg, 0)?;
        if let Some(GroundVal::Bits(_value)) = pre_post_states.pre_registers.get(&("zDDC_EL3", vec![])) {
            write_aldr_off(&mut asm_file, entry_reg, exit_reg, 3)?;
            write_msr_cap(&mut asm_file, &REG_DDC_EL3, entry_reg)?;
            writeln!(asm_file, "\tisb")?;
        }
        write_aldr_off(&mut asm_file, entry_reg, exit_reg, 1)?;
        write_aldr_off(&mut asm_file, exit_reg, exit_reg, 2)?;
	if target.run_in_el0() {
	    write_msr_cap(&mut asm_file, &REG_CELR_EL3, entry_reg)?;
	    writeln!(asm_file, "\t eret")?;
	} else {
            write_br(&mut asm_file, entry_reg)?;
	}
    } else {
        writeln!(asm_file, "\tldr x{}, =test_start", entry_reg)?;
        writeln!(asm_file, "\tldr x{}, =finish", exit_reg)?;
        writeln!(asm_file, "\tbr x{}", entry_reg)?;
    }

    // ------

    writeln!(asm_file, "finish:")?;
    if target.has_capabilities() {
        writeln!(asm_file, "\t/* Reconstruct general DDC from PCC, keep MMU and cache on for comparisons */")?;
        write_cvtp(&mut asm_file, entry_reg, 0)?;
        write_scvalue(&mut asm_file, entry_reg, entry_reg, 31)?; // 31 is ZR
        write_msr_cap(&mut asm_file, &REG_DDC_EL3, entry_reg)?;
        writeln!(asm_file, "\tldr x{}, =0x30851035", entry_reg)?;
        writeln!(asm_file, "\tmsr SCTLR_EL3, x{}", entry_reg)?;
        writeln!(asm_file, "\tisb")?;
    }

    /* Check the processor flags before they're trashed */
    if flags.post_nzcv_mask == 0 {
        writeln!(asm_file, "\t/* No processor flags to check */")?;
    } else {
        writeln!(asm_file, "\t/* Check processor flags */")?;
        // Even if we reached here via processor exceptions the flags should be unchanged
        writeln!(asm_file, "\tmrs x{}, nzcv", entry_reg)?;
        writeln!(asm_file, "\tubfx x{0}, x{0}, #28, #4", entry_reg)?;
        writeln!(asm_file, "\tmov x{}, #{:#03x}", exit_reg, flags.post_nzcv_mask)?;
        writeln!(asm_file, "\tand x{0}, x{0}, x{1}", entry_reg, exit_reg)?;
        writeln!(asm_file, "\tcmp x{}, #{:#03x}", entry_reg, flags.post_nzcv_value)?;
        writeln!(asm_file, "\tb.ne comparison_fail")?;
    }
    writeln!(asm_file, "\t/* Check registers */")?;
    if target.has_capabilities() {
        writeln!(asm_file, "\tldr x{}, =final_cap_values", entry_reg)?;
        for (i, (reg, _value)) in post_gprs.iter().enumerate() {
            write_ldr_off(&mut asm_file, exit_reg, entry_reg, i as u32)?;
            write_chkeq(&mut asm_file, *reg, exit_reg)?;
            writeln!(asm_file, "\tb.ne comparison_fail")?;
        }
    } else {
        for (reg, value) in get_numbered_registers(T::gpr_prefix(), T::gpr_pad(), 32, &pre_post_states.post_registers) {
            writeln!(asm_file, "\tldr x{}, ={:#x}", entry_reg, value.lower_u64())?;
            writeln!(asm_file, "\tcmp x{}, x{}", entry_reg, reg)?;
            writeln!(asm_file, "\tb.ne comparison_fail")?;
        }
    }
    let vector_registers = get_vector_registers(&pre_post_states.post_registers);
    if !vector_registers.is_empty() {
        writeln!(asm_file, "\t/* Check vector registers */")?;
        for (reg, value) in vector_registers {
            writeln!(asm_file, "\tldr x{}, ={:#x}", entry_reg, value.lower_u64())?;
            writeln!(asm_file, "\tmov x{}, v{}.d[0]", exit_reg, reg)?;
            writeln!(asm_file, "\tcmp x{}, x{}", entry_reg, exit_reg)?;
            writeln!(asm_file, "\tb.ne comparison_fail")?;
            writeln!(asm_file, "\tldr x{}, ={:#x}", entry_reg, value.shiftr(64).lower_u64())?;
            writeln!(asm_file, "\tmov x{}, v{}.d[1]", exit_reg, reg)?;
            writeln!(asm_file, "\tcmp x{}, x{}", entry_reg, exit_reg)?;
            writeln!(asm_file, "\tb.ne comparison_fail")?;
        }
    }
    if !post_system_registers.is_empty() {
        writeln!(asm_file, "\t/* Check system registers */")?;
        for (reg, value) in &post_system_registers {
            if reg == "ESR_EL1" {
                let value = value.lower_u64();
                write_cap_esr_check(&mut asm_file, value, entry_reg, exit_reg)?;
            } else {
                let actual_reg = if reg == "PCC" {
                    assert!(target.run_in_el0());
                    "ELR_EL1"
                } else {
                    reg
                };
                if let Some(operand) = system_cap_map.get(actual_reg) {
                    writeln!(asm_file, "\tldr x{}, =final_{}_value", entry_reg, reg)?;
                    write_ldr_off(&mut asm_file, entry_reg, entry_reg, 0)?;
                    write_mrs_cap(&mut asm_file, exit_reg, operand)?;
                    write_chkeq(&mut asm_file, entry_reg, exit_reg)?;
                    writeln!(asm_file, "\tb.ne comparison_fail")?;
                } else {
                    writeln!(asm_file, "\tldr x{}, ={:#x}", entry_reg, value.lower_u64())?;
                    writeln!(asm_file, "\tmrs x{}, {}", exit_reg, reg)?;
                    writeln!(asm_file, "\tcmp x{}, x{}", entry_reg, exit_reg)?;
                    writeln!(asm_file, "\tb.ne comparison_fail")?;
                }
            }
        }
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
    if target.has_capabilities() {
        writeln!(asm_file, "\tldr x0, =final_tag_set_locations")?;
        writeln!(asm_file, "check_set_tags_loop:")?;
        writeln!(asm_file, "\tldr x1, [x0], #8")?;
        writeln!(asm_file, "\tcbz x1, check_set_tags_end")?;
        write_ldr_off(&mut asm_file, 3, 1, 0)?;
        write_chktgd(&mut asm_file, 3)?;
        writeln!(asm_file, "\tb.cc comparison_fail")?;
        writeln!(asm_file, "\tb check_set_tags_loop")?;
        writeln!(asm_file, "check_set_tags_end:")?;
        
        writeln!(asm_file, "\tldr x0, =final_tag_unset_locations")?;
        writeln!(asm_file, "check_unset_tags_loop:")?;
        writeln!(asm_file, "\tldr x1, [x0], #8")?;
        writeln!(asm_file, "\tcbz x1, check_unset_tags_end")?;
        write_ldr_off(&mut asm_file, 3, 1, 0)?;
        write_chktgd(&mut asm_file, 3)?;
        writeln!(asm_file, "\tb.cs comparison_fail")?;
        writeln!(asm_file, "\tb check_unset_tags_loop")?;
        writeln!(asm_file, "check_unset_tags_end:")?;
    }
    writeln!(asm_file, "\t/* Done print message */")?;
    if target.has_capabilities() {
        writeln!(asm_file, "\t/* turn off MMU */")?;
        writeln!(asm_file, "\tldr x{}, =0x30850030", entry_reg)?;
        writeln!(asm_file, "\tmsr SCTLR_EL3, x{}", entry_reg)?;
        writeln!(asm_file, "\tisb")?;
    }
    writeln!(asm_file, "\tldr x0, =ok_message")?;
    writeln!(asm_file, "\tb write_tube")?;
    writeln!(asm_file, "\t.global comparison_fail")?;
    writeln!(asm_file, "comparison_fail:")?;
    // Repeat DDC because this is also the exception entry path
    if target.has_capabilities() {
        writeln!(asm_file, "\t/* Reconstruct general DDC from PCC, turn off MMU */")?;
        write_cvtp(&mut asm_file, entry_reg, 0)?;
        write_scvalue(&mut asm_file, entry_reg, entry_reg, 31)?; // 31 is ZR
        write_msr_cap(&mut asm_file, &REG_DDC_EL3, entry_reg)?;
        writeln!(asm_file, "\tldr x{}, =0x30850030", entry_reg)?;
        writeln!(asm_file, "\tmsr SCTLR_EL3, x{}", entry_reg)?;
        writeln!(asm_file, "\tisb")?;
    }
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

    writeln!(asm_file, "")?;
    write_main_memory(&mut asm_file, &mut ld_file, &pre_post_states)?;

    if target.has_capabilities() {
    writeln!(asm_file, "")?;
        write_capability_data(target, &mut asm_file, &gprs, &post_gprs, &system_registers, &post_system_registers, &pre_post_states, &system_cap_map)?;
    }

    writeln!(asm_file, "")?;
    writeln!(ld_file, ".vector_table 0x0000000010310000 : {{ *(vector_table) }}")?;
    writeln!(asm_file, ".section vector_table, #alloc, #execinstr")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    if target.run_in_el0() {
	writeln!(asm_file, "\tb finish")?;
    } else {
	writeln!(asm_file, "\tb comparison_fail")?;
    }
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;
    writeln!(asm_file, "\t.balign 128")?;
    writeln!(asm_file, "\tb comparison_fail")?;

    if target.run_in_el0() {
        let exit_address = get_exit_address(&pre_post_states);

	writeln!(asm_file, "")?;
        // Execute at the non-writable 0x5... virtual address, but load at the 0x1... physical address
	writeln!(ld_file, ".vector_table_el1 0x0000000050320000 : AT(0x0000000010320000) {{ *(vector_table_el1) }}")?;
	writeln!(asm_file, ".section vector_table_el1, #alloc, #execinstr")?;
        let mut off = 0;
        while off < 0x800 {
	    if off != 0 { writeln!(asm_file, "\t.balign 128")?; }
	    write_el1_vector(&mut asm_file, entry_reg, exit_reg, exit_address, off)?;
            off += 0x80;
        }
    }
    
    writeln!(asm_file, "")?;
    writeln!(asm_file, "\t/* Translation table, two entries for the bottom GB, capabilities allowed */")?;
    writeln!(ld_file, ".text_tt 0x0000000010400000 : {{ *(text_tt) }}")?;
    writeln!(asm_file, ".section text_tt, #alloc, #execinstr")?;
    writeln!(asm_file, "\t.align 12")?;
    writeln!(asm_file, "\t.global tt_l1_base")?;
    writeln!(asm_file, "tt_l1_base:")?;
    writeln!(asm_file, "\t.dword 0x3000000000000741")?;
    writeln!(asm_file, "\t.dword 0x30000000000007c1 // No write permission so that EL1 can execute")?;
    writeln!(asm_file, "\t.fill 4088, 1, 0")?;

    writeln!(ld_file, "}}")?;
    writeln!(ld_file, "ENTRY(preamble)")?;
    writeln!(ld_file, "trickbox = 0x13000000;")?;

    Ok(())
}

#[derive(Debug)]
pub struct BuildError(String);

impl std::fmt::Display for BuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl Error for BuildError {}

pub fn build_elf_file<B>(isa: &ISAConfig<B>, base_name: &str) -> Result<(), BuildError> {
    let assembler_result = isa
        .assembler
        .command()
        .args(&["-march=armv8.2-a", "-o", &format!("{}.o", base_name), &format!("{}.s", base_name)])
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
