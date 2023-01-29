use crate::extract_state::{GroundVal, PrePostStates};
use crate::target::Target;

use isla_lib::bitvector::BV;
use isla_lib::zencode;

use std::collections::{HashMap};
use std::convert::TryFrom;
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
    for (region, contents) in pre_post_states.code.iter() {
        let mut ptr = region.start;
        // TODO: chunking will have to change for x86_64
        for word in contents.chunks(4) {
            let word_u32 = u32::from_le_bytes(TryFrom::try_from(word)?);
            write!(test_file, "mem {:#x} 32 {:#010x}", ptr, word_u32)?;
            if let Some(description) = instr_map.get(&B::new(word_u32 as u64, 32)) {
                writeln!(test_file, " // {}", description)?;
            } else {
                writeln!(test_file)?;
            }
            ptr += 4;
        }
    }

    for (region, contents) in pre_post_states.pre_memory.iter() {
        for (i, byte) in contents.iter().enumerate() {
            writeln!(test_file, "mem {:#x} 8 {:#04x}", region.start + i as u64, byte)?;
        }
    }

    // TODO: CHERI tags

    let target_regs = target.regs();

    for ((zregister, accessor), val) in pre_post_states.pre_registers.iter() {
        let register = zencode::decode(zregister);
        if target_regs.iter().any(|(r,a)| *r == register && a == accessor) {
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

    let post_pc =
        match pre_post_states.post_registers.get(&("z_PC", vec![])) {
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

    for ((zregister, accessor), val) in pre_post_states.post_registers.iter() {
        let register = zencode::decode(zregister);
        if T::is_gpr(zregister).is_some() || post_regs.iter().any(|(r,a)| *r == register && a == accessor) {
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
