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
    _instr_map: &HashMap<B, String>,
    pre_post_states: PrePostStates<B>,
    init_pc: u64,
    steps: u64,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut test_file = File::create(&format!("{}.test", base_name))?;

    let mut pre_tag_mem: HashMap<u64, bool> = HashMap::new();
    for (region, tags) in pre_post_states.pre_tag_memory.iter() {
        for (i, tag) in tags.iter().enumerate() {
            pre_tag_mem.insert(region.start + i as u64, *tag);
        }
    }

    let alignment = 1 << T::pc_alignment_pow();
    for (region, contents) in pre_post_states.code.iter() {
        let mut ptr = region.start;
        for chunk in contents.chunks(alignment as usize) {
            let chunk_le: Vec<u8> = chunk.iter().cloned().rev().collect();
            let chunk_b = B::from_bytes(&chunk_le);
            write!(test_file, "mem {:#x} {} 0x{:x}", ptr, chunk_b.len(), chunk_b)?;
            if let Some(description) = pre_post_states.instruction_locations.get(&ptr) {
                writeln!(test_file, " // {}", description)?;
            } else {
                writeln!(test_file)?;
            }
            ptr += alignment as u64;
        }
    }

    // TODO: handle unaligned stuff properly
    let alignment = 16;
    for (region, contents) in pre_post_states.pre_memory.iter() {
        let mut ptr = region.start;
        for chunk in contents.chunks(alignment) {
            let chunk_le: Vec<u8> = chunk.iter().cloned().rev().collect();
            let chunk_b = B::from_bytes(&chunk_le);
            let tag =
                if target.has_capabilities() {
                    match pre_tag_mem.get(&ptr) {
                        Some(true) => " t",
                        Some(false) => " f",
                        None => "",
                    }
                } else {
                    ""
                };
            writeln!(test_file, "mem {:#x} {} 0x{:x}{}", ptr, chunk_b.len(), chunk_b, tag)?;
            ptr += alignment as u64;
        }
    }

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
            if let GroundVal::Bits(bits, m) = val {
                assert!(m.is_zero());
                writeln!(test_file, "reg {} {} 0x{:x}", names.join("."), bits.len(), bits)?;
            } else {
                println!("Bad value for {}: {:?}", names.join("."), val);
            }
        }
    }

    let (pc_reg, pc_acc) = target.pc_reg();
    let pc_acc: Vec<GVAccessor<String>> = pc_acc.iter().map(|a| match a {
        GVAccessor::Field(s) => GVAccessor::Field(zencode::encode(s)),
        GVAccessor::Element(i) => GVAccessor::Element(*i),
    }).collect();
    let pc_acc: Vec<GVAccessor<&str>> = pc_acc.iter().map(|a| match a {
        GVAccessor::Field(s) => GVAccessor::Field(s.as_str()),
        GVAccessor::Element(i) => GVAccessor::Element(*i),
    }).collect();
    let post_pc =
        match pre_post_states.post_registers.get(&(&pc_reg, pc_acc)) {
            Some(GroundVal::Bits(bits, m)) => {
                assert!(m.is_zero());
                bits
            }
            Some(v) => panic!("Bad post-state PC: {:?}", v),
            None => panic!("Post-state PC missing"),
        };

    writeln!(test_file, "RUN start {:#010x} stop {:#010x} steps {}", init_pc, post_pc.lower_u64(), steps)?;

    for (region, contents) in pre_post_states.post_memory.iter() {
        for (i, byte) in contents.iter().enumerate() {
            writeln!(test_file, "mem {:#x} 8 {:#04x}", region.start + i as u64, byte)?;
        }
    }

    if target.has_capabilities() {
        for (ptr, tag) in pre_post_states.post_tag_memory {
            let tag = if tag {"t"} else {"f"};
            writeln!(test_file, "tag {:#x} {}", ptr, tag)?;
        }
    }

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
            if let GroundVal::Bits(bits, undefs) = val {
                if undefs.is_zero() {
                    writeln!(test_file, "reg {} {} 0x{:x}", names.join("."), bits.len(), bits)?;
                } else {
                    writeln!(test_file, "reg {} {} 0x{:x} mask 0x{:x}", names.join("."), bits.len(), bits, !*undefs)?;
                }
            } else {
                println!("Bad value for {}: {:?}", names.join("."), val);
            }
        }
    }

    writeln!(test_file, "END")?;

    Ok(())
}
