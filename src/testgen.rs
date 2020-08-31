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

use isla_axiomatic::litmus::assemble_instruction;
use isla_lib::config::ISAConfig;
use isla_lib::init::{initialize_architecture, Initialized};
use rand::Rng;
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::ops::Range;
use std::process::exit;

// TODO: allow B64 or B129
use isla_lib::concrete::{bitvector129::B129, BV};
use isla_lib::executor::Frame;
use isla_lib::ir::*;
use isla_lib::memory::{Address, Memory};
use isla_lib::simplify::write_events;
use isla_lib::smt::{Checkpoint, Event};
use isla_lib::zencode;

use isla_testgen::asl_tag_files;
use isla_testgen::execution::*;
use isla_testgen::extract_state;
use isla_testgen::generate_object;
use isla_testgen::target;
use isla_testgen::target::Target;

use isla::opts;
use opts::CommonOpts;

fn main() {
    let code = isla_main();
    unsafe { isla_lib::smt::finalize_solver() };
    exit(code)
}

fn parse_instruction_masks(little_endian: bool, args: &[String]) -> Vec<(&str, Option<u32>)> {
    let mut iter = args.iter().peekable();
    let mut v: Vec<(&str, Option<u32>)> = vec![];
    loop {
        let s = match iter.next() {
            None => break,
            Some(s) => s,
        };
        let p = iter.peek().copied();
        let m: Option<u32> = match p {
            None => None,
            Some(s) => {
                if s.starts_with("mask:") {
                    iter.next();
                    match u32::from_str_radix(&s[5..], 16) {
                        Ok(m) => Some(if little_endian { u32::from_le(m) } else { u32::from_be(m) }),
                        Err(e) => {
                            eprintln!("Could not parse mask: {}", e);
                            exit(1)
                        }
                    }
                } else {
                    None
                }
            }
        };
        v.push((s, m));
    }
    v
}

fn instruction_opcode<B: BV>(
    little_endian: bool,
    encodings: &asl_tag_files::Encodings,
    isa_config: &ISAConfig<B>,
    instruction: &str,
) -> (B, bool) {
    let (opcode, random) = if instruction == "_" {
        let (opcode, description) = encodings.random(asl_tag_files::Encoding::A64);
        println!("Instruction {:#010x}: {}", opcode, description);
        (opcode.to_le_bytes(), true)
    } else if instruction.starts_with("0x") {
        println!("Instruction {}", instruction);
        match u32::from_str_radix(&instruction[2..], 16) {
            Ok(opcode) => (opcode.to_le_bytes(), false),
            Err(e) => {
                eprintln!("Could not parse instruction: {}", e);
                exit(1)
            }
        }
    } else {
        println!("Instruction {}", instruction);
        match assemble_instruction(&instruction, &isa_config) {
            Ok(bytes) => {
                let mut opcode: [u8; 4] = Default::default();
                opcode.copy_from_slice(&bytes);
                (opcode, false)
            }
            Err(msg) => {
                eprintln!("Could not assemble instruction: {}", msg);
                exit(1);
            }
        }
    };
    (B::from_u32(if little_endian { u32::from_le_bytes(opcode) } else { u32::from_be_bytes(opcode) }), random)
}

fn isla_main() -> i32 {
    let mut opts = opts::common_opts();
    opts.optopt("", "max-retries", "Stop if this many instructions in a row are useless", "<retries>");
    opts.optopt("a", "target-arch", "target architecture", "aarch64/morello");
    opts.optopt("e", "endianness", "instruction encoding endianness (little default)", "big/little");
    opts.optopt("t", "tag-file", "parse instruction encodings from tag file", "<file>");
    opts.optopt("o", "output", "base name for output files", "<file>");
    opts.optopt("n", "number-gens", "number of tests to attempt to generate", "<number>");
    opts.optmulti("", "exclude", "exclude matching instructions from tag file", "<regexp>");
    opts.optmulti("k", "stop-fn", "stop executions early if they reach this function", "<function name>");
    opts.optflag("", "events", "dump final events");
    opts.optflag("", "all-events", "dump events for every behaviour");

    let mut hasher = Sha256::new();
    let (matches, arch) = opts::parse::<B129>(&mut hasher, &opts);

    match matches.opt_str("target-arch").as_deref().unwrap_or("aarch64") {
        "aarch64" => testgen_main(target::Aarch64 {}, hasher, opts, matches, arch),
        "morello" => testgen_main(target::Morello {}, hasher, opts, matches, arch),
        target_str => {
            eprintln!("Unknown target architecture: {}", target_str);
            1
        }
    }
}

fn parse_function_names<B>(names: Vec<String>, shared_state: &SharedState<B>) -> HashSet<Name> {
    let mut set = HashSet::new();
    for f in names {
        let fz = zencode::encode(&f);
        let n = shared_state
            .symtab
            .get(&fz)
            .or_else(|| shared_state.symtab.get(&f))
            .unwrap_or_else(|| panic!("Function {} not found", f));
        set.insert(n);
    }
    set
}

fn testgen_main<T: Target, B: BV>(
    target: T,
    mut hasher: Sha256,
    opts: getopts::Options,
    matches: getopts::Matches,
    arch: Vec<Def<String, B>>,
) -> i32 {
    let CommonOpts { num_threads, mut arch, symtab, isa_config } =
        opts::parse_with_arch(&mut hasher, &opts, &matches, &arch);

    let max_retries = matches.opt_get_default("max-retries", 10).expect("Bad max-retries argument");
    let number_gens = matches.opt_get_default("number-gens", 1).expect("Bad number-gens argument");

    let exclusions = matches.opt_strs("exclude");

    let encodings = match matches.opt_str("tag-file") {
        Some(name) => asl_tag_files::read_tag_file(&name, &exclusions),
        None => asl_tag_files::Encodings::default(),
    };

    let register_types: HashMap<Name, Ty<Name>> = arch
        .iter()
        .filter_map(|d| match d {
            Def::Register(reg, ty) => Some((*reg, ty.clone())),
            _ => None,
        })
        .collect();

    let Initialized { regs, mut lets, shared_state } =
        initialize_architecture(&mut arch, symtab, &isa_config, AssertionMode::Optimistic);

    let init_pc = isa_config.thread_base;
    // NB: The current aarch64 model needs this, however we explicitly
    // override the PC when setting up the registers.
    lets.insert(ELF_ENTRY, UVal::Init(Val::I128(init_pc as i128)));

    let stop_functions = parse_function_names(matches.opt_strs("stop-fn"), &shared_state);

    let little_endian = match matches.opt_str("endianness").as_deref() {
        Some("little") | None => true,
        Some("big") => false,
        Some(_) => {
            eprintln!("--endianness argument must be one of either `big` or `little`");
            exit(1)
        }
    };

    let dump_events = matches.opt_present("events");
    let dump_all_events = matches.opt_present("all-events");

    let symbolic_regions = [0x1000..0x2000];
    let symbolic_code_regions = [isa_config.thread_base..isa_config.thread_top];
    let mut memory = Memory::new();
    for r in &symbolic_regions {
        memory.add_symbolic_region(r.clone());
    }
    for r in &symbolic_code_regions {
        memory.add_symbolic_code_region(r.clone());
    }
    memory.log();

    let instructions = parse_instruction_masks(little_endian, &matches.free);

    let (frame, checkpoint) = init_model(&shared_state, lets, regs, &memory);
    let (frame, checkpoint) = setup_init_regs(&shared_state, frame, checkpoint, &register_types, init_pc, &target);

    let base_name = &matches.opt_str("output").unwrap_or(String::from("test"));

    let testconf = TestConf {
        instructions: &instructions,
        max_retries,
        shared_state: &shared_state,
        num_threads,
        dump_events,
        dump_all_events,
        little_endian,
        isa_config: &isa_config,
        encodings: &encodings,
        stop_functions: &stop_functions,
        register_types: &register_types,
        symbolic_regions: &symbolic_regions,
        symbolic_code_regions: &symbolic_code_regions,
    };

    if number_gens > 1 {
        for i in 0..number_gens {
            generate_test(&target, &testconf, frame.clone(), checkpoint.clone(), &format!("{}{}", base_name, i + 1));
        }
    } else if number_gens == 1 {
        generate_test(&target, &testconf, frame, checkpoint, base_name);
    }

    0
}

struct TestConf<'ir, B> {
    instructions: &'ir [(&'ir str, Option<u32>)],
    max_retries: i32,
    shared_state: &'ir SharedState<'ir, B>,
    num_threads: usize,
    dump_events: bool,
    dump_all_events: bool,
    little_endian: bool,
    isa_config: &'ir ISAConfig<B>,
    encodings: &'ir asl_tag_files::Encodings,
    stop_functions: &'ir HashSet<Name>,
    register_types: &'ir HashMap<Name, Ty<Name>>,
    symbolic_regions: &'ir [Range<Address>],
    symbolic_code_regions: &'ir [Range<Address>],
}

fn generate_test<'ir, B: BV, T: Target>(
    target: &T,
    conf: &TestConf<'ir, B>,
    mut frame: Frame<'ir, B>,
    mut checkpoint: Checkpoint<B>,
    basename: &str,
) {
    let run_instruction_function = T::run_instruction_function();

    let mut opcode_vars = vec![];

    let mut opcode_index = 0;
    let mut rng = rand::thread_rng();
    for (instruction, opcode_mask) in conf.instructions {
        let mut random_attempts_left = conf.max_retries;
        loop {
            let (opcode, repeat) = instruction_opcode(conf.little_endian, conf.encodings, conf.isa_config, instruction);
            let mask_str = match opcode_mask {
                None => "none".to_string(),
                Some(m) => format!("{:#010x}", m),
            };
            eprintln!("opcode: {:#010x}  mask: {}", opcode, mask_str);
            let (opcode_var, op_checkpoint) =
                setup_opcode(conf.shared_state, &frame, opcode, *opcode_mask, checkpoint.clone());
            let mut continuations = run_model_instruction(
                &run_instruction_function,
                conf.num_threads,
                conf.shared_state,
                &frame,
                op_checkpoint,
                opcode_var,
                conf.stop_functions,
                conf.dump_all_events,
            );
            let num_continuations = continuations.len();
            if num_continuations > 0 {
                let (f, c) = continuations.remove(rng.gen_range(0, num_continuations));
                eprintln!("{} successful execution(s)", num_continuations);
                opcode_vars.push((format!("opcode {}", opcode_index), RegSource::Symbolic(opcode_var)));
                opcode_index += 1;
                frame = f;
                checkpoint = c;
                break;
            } else {
                eprintln!("No successful executions");
                if repeat {
                    random_attempts_left -= 1;
                    if random_attempts_left == 0 {
                        eprintln!("Retried too many times");
                        exit(1);
                    }
                } else {
                    eprintln!("Unable to continue");
                    exit(1);
                }
            }
        }
    }

    let (entry_reg, exit_reg, checkpoint) = finalize(target, conf.shared_state, &frame, checkpoint);

    eprintln!("Complete");

    if conf.dump_events {
        let trace = checkpoint.trace().as_ref().expect("No trace!");
        let mut events = trace.to_vec();
        let events: Vec<Event<B>> = events.drain(..).cloned().rev().collect();
        write_events(&mut std::io::stdout(), &events, &conf.shared_state.symtab);
    }

    println!("Initial state extracted from events:");
    let initial_state = extract_state::interrogate_model(
        target,
        conf.isa_config,
        checkpoint,
        conf.shared_state,
        conf.register_types,
        conf.symbolic_regions,
        conf.symbolic_code_regions,
    )
    .expect("Error extracting state");
    generate_object::make_asm_files(target, basename, initial_state, entry_reg, exit_reg)
        .expect("Error generating object file");
    generate_object::build_elf_file(conf.isa_config, basename);
}
