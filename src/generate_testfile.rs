use crate::extract_state::{GroundVal, GVAccessor, PrePostStates};
use crate::target::Target;

use isla_lib::bitvector::BV;
use isla_lib::zencode;

use std::collections::{HashMap};
use std::fs::File;
use std::io::Write;

pub fn make_testfile<B: BV, T: Target>(
    target: &T,
    base_name: &str,
    instr_map: &HashMap<B, String>,
    pre_post_states: PrePostStates<B>,
    init_pc: u64,
    steps: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut test_file = File::create(&format!("{}.test", base_name))?;
    let alignment = 1 << T::pc_alignment_pow();
    for (region, contents) in pre_post_states.code.iter() {
        let mut ptr = region.start;
        for chunk in contents.chunks(alignment as usize) {
            let chunk_le: Vec<u8> = chunk.iter().cloned().rev().collect();
            let chunk_b = B::from_bytes(&chunk_le);
            write!(test_file, "mem {:#x} {} 0x{:x}", ptr, chunk_b.len(), chunk_b)?;
            if let Some(description) = instr_map.get(&chunk_b) {
                writeln!(test_file, " // {}", description)?;
            } else {
                writeln!(test_file)?;
            }
            ptr += alignment as u64;
        }
    }

    for (region, contents) in pre_post_states.pre_memory.iter() {
        for (i, byte) in contents.iter().enumerate() {
            writeln!(test_file, "mem {:#x} 8 {:#04x}", region.start + i as u64, byte)?;
        }
    }

    // TODO: CHERI tags

    let target_regs = target.regs();

    for ((zregister, zaccessor), val) in pre_post_states.pre_registers.iter() {
        let register = zencode::decode(zregister);
        let accessor: Vec<GVAccessor<String>> = zaccessor.iter().map(|a| match a {
            GVAccessor::Field(s) => GVAccessor::Field(zencode::decode(s)),
            GVAccessor::Element(i) => GVAccessor::Element(*i),
        }).collect();
        if target_regs.iter().any(|(r,a)| *r == *register && *a == accessor) {
            let mut names: Vec<String> = vec![register];
            let mut accessors: Vec<String> = accessor.iter().map(|acc| acc.to_string()).collect();
            names.append(&mut accessors);
            if let GroundVal::Bits(bits) = val {
                writeln!(test_file, "reg {} {} 0x{:x}", names.join("."), bits.len(), bits)?;
            } else {
                println!("Bad value for {}: {:?}", names.join("."), val);
            }
        }
    }

    let post_pc =
        match pre_post_states.post_registers.get(&(T::pc_reg(), vec![])) {
            Some(GroundVal::Bits(bits)) => bits,
            Some(v) => panic!("Bad post-state PC: {:?}", v),
            None => panic!("Post-state PC missing"),
        };

    writeln!(test_file, "RUN start {:#010x} stop {:#010x} steps {}", init_pc, post_pc.lower_u64(), steps)?;

    for (region, contents) in pre_post_states.post_memory.iter() {
        for (i, byte) in contents.iter().enumerate() {
            writeln!(test_file, "mem {:#x} 8 {:#04x}", region.start + i as u64, byte)?;
        }
    }

    // TODO: CHERI tags

    // TODO: we can probably check more with gdb than the harnesses
    let post_regs = target.post_regs();

    for ((zregister, zaccessor), val) in pre_post_states.post_registers.iter() {
        let register = zencode::decode(zregister);
        let accessor: Vec<GVAccessor<String>> = zaccessor.iter().map(|a| match a {
            GVAccessor::Field(s) => GVAccessor::Field(zencode::decode(s)),
            GVAccessor::Element(i) => GVAccessor::Element(*i),
        }).collect();
        if T::is_gpr(zregister).is_some() || post_regs.iter().any(|(r,a)| *r == register && *a == *accessor) {
            let mut names: Vec<String> = vec![register.to_string()];
            let mut accessors: Vec<String> = accessor.iter().map(|acc| acc.to_string()).collect();
            names.append(&mut accessors);
            if let GroundVal::Bits(bits) = val {
                writeln!(test_file, "reg {} {} 0x{:x}", names.join("."), bits.len(), bits)?;
            } else {
                println!("Bad value for {}: {:?}", names.join("."), val);
            }
        }
    }

    writeln!(test_file, "END")?;

    Ok(())
}
