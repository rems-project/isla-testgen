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

use crossbeam::queue::SegQueue;
use std::collections::{HashMap, HashSet};
use std::process::exit;
use std::sync::Arc;
use std::time::Instant;

use crate::target::Target;

use isla_lib::concrete::BV;
use isla_lib::error::ExecError;
use isla_lib::executor;
use isla_lib::executor::{freeze_frame, Frame, LocalFrame};
use isla_lib::ir::*;
use isla_lib::memory::{Memory, SmtKind};
use isla_lib::simplify::simplify;
use isla_lib::simplify::write_events;
use isla_lib::smt;
use isla_lib::smt::smtlib;
use isla_lib::smt::{Checkpoint, Event, Model, SmtResult, Solver, Sym};
use isla_lib::zencode;
use isla_lib::{log, log_from};

fn smt_read_exp(memory: Sym, addr_exp: &smtlib::Exp, bytes: u64) -> smtlib::Exp {
    use smtlib::Exp;
    // TODO: endianness?
    let mut mem_exp = Exp::Select(Box::new(Exp::Var(memory)), Box::new(addr_exp.clone()));
    for i in 1..bytes {
        mem_exp = Exp::Concat(
            Box::new(Exp::Select(
                Box::new(Exp::Var(memory)),
                Box::new(Exp::Bvadd(Box::new(addr_exp.clone()), Box::new(Exp::Bits64(i as u64, 64)))),
            )),
            Box::new(mem_exp),
        )
    }
    mem_exp
}

#[derive(Debug, Clone)]
struct SeqMemory {
    read_ifetch: EnumMember,
    memory_var: Sym,
}

impl<B: BV> isla_lib::memory::MemoryCallbacks<B> for SeqMemory {
    fn symbolic_read(
        &self,
        regions: &[isla_lib::memory::Region<B>],
        solver: &mut Solver<B>,
        value: &Val<B>,
        read_kind: &Val<B>,
        address: &Val<B>,
        bytes: u32,
    ) {
        use isla_lib::primop::smt_value;
        use isla_lib::smt::smtlib::{Def, Exp};

        let read_exp = smt_value(value).expect(&format!("Bad memory read value {:?}", value));
        let addr_exp = smt_value(address).expect(&format!("Bad read address value {:?}", address));
        solver.add(Def::Assert(Exp::Eq(
            Box::new(read_exp),
            Box::new(smt_read_exp(self.memory_var, &addr_exp, bytes as u64)),
        )));
        let kind = match read_kind {
            Val::Enum(e) => {
                if *e == self.read_ifetch {
                    SmtKind::ReadInstr
                } else {
                    SmtKind::ReadData
                }
            }
            _ => SmtKind::ReadData,
        };
        let address_constraint = isla_lib::memory::smt_address_constraint(regions, &addr_exp, bytes, kind, solver);
        solver.add(Def::Assert(address_constraint));
    }

    fn symbolic_write(
        &mut self,
        regions: &[isla_lib::memory::Region<B>],
        solver: &mut Solver<B>,
        _value: Sym,
        _read_kind: &Val<B>,
        address: &Val<B>,
        data: &Val<B>,
        bytes: u32,
    ) {
        use isla_lib::primop::smt_value;
        use isla_lib::smt::smtlib::{Def, Exp};

        let data_exp = smt_value(data).expect(&format!("Bad memory read value {:?}", data));
        let addr_exp = smt_value(address).expect(&format!("Bad read address value {:?}", address));
        // TODO: endianness?
        let mut mem_exp = Exp::Store(
            Box::new(Exp::Var(self.memory_var)),
            Box::new(addr_exp.clone()),
            Box::new(Exp::Extract(7, 0, Box::new(data_exp.clone()))),
        );
        for i in 1..bytes {
            mem_exp = Exp::Store(
                Box::new(mem_exp),
                Box::new(Exp::Bvadd(Box::new(addr_exp.clone()), Box::new(Exp::Bits64(i as u64, 64)))),
                Box::new(Exp::Extract(i * 8 + 7, i * 8, Box::new(data_exp.clone()))),
            )
        }
        self.memory_var = solver.fresh();
        solver.add(Def::DefineConst(self.memory_var, mem_exp));
        let kind = SmtKind::WriteData;
        let address_constraint = isla_lib::memory::smt_address_constraint(regions, &addr_exp, bytes, kind, solver);
        solver.add(Def::Assert(address_constraint));
    }
}

fn postprocess<'ir, B: BV>(
    tid: usize,
    _task_id: usize,
    local_frame: LocalFrame<'ir, B>,
    shared_state: &SharedState<'ir, B>,
    mut solver: Solver<B>,
    _events: &Vec<Event<B>>,
) -> Result<(Frame<'ir, B>, Checkpoint<B>), String> {
    use isla_lib::smt::smtlib::{Def, Exp};

    log_from!(tid, log::VERBOSE, "Postprocessing");

    // Ensure the new PC can be placed in memory
    // (currently this is used to prevent an exception)
    let pc_id = shared_state.symtab.lookup("z_PC");
    let pc = local_frame.regs().get(&pc_id).unwrap();
    let pc_exp = match pc {
        UVal::Init(Val::Symbolic(v)) => Exp::Var(*v),
        UVal::Init(Val::Bits(b)) => Exp::Bits64(b.lower_u64(), b.len()),
        _ => panic!("Bad PC value {:?}", pc),
    };
    let pc_constraint = local_frame.memory().smt_address_constraint(&pc_exp, 4, SmtKind::ReadInstr, &mut solver);
    solver.add(Def::Assert(pc_constraint));

    let result = match solver.check_sat() {
        SmtResult::Sat => Ok((freeze_frame(&local_frame), smt::checkpoint(&mut solver))),
        SmtResult::Unsat => Err(String::from("unsatisfiable")),
        SmtResult::Unknown => Err(String::from("solver returned unknown")),
    };
    log_from!(tid, log::VERBOSE, "Postprocessing complete");
    result
}

// Get a single opcode for debugging
fn get_opcode<B: BV>(checkpoint: Checkpoint<B>, opcode_var: Sym) -> Result<u32, String> {
    let cfg = smt::Config::new();
    cfg.set_param_value("model", "true");
    let ctx = smt::Context::new(cfg);
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    match solver.check_sat() {
        SmtResult::Sat => (),
        SmtResult::Unsat => return Err(String::from("Unsatisfiable at recheck")),
        SmtResult::Unknown => return Err(String::from("Solver returned unknown at recheck")),
    };
    let mut model = Model::new(&solver);
    log!(log::VERBOSE, format!("Model: {:?}", model));
    let opcode = model.get_var(opcode_var).unwrap().unwrap();
    match opcode {
        smt::smtlib::Exp::Bits64(bits, _) => Ok(bits as u32),
        _ => Err(String::from("Bad model value")),
    }
}

pub enum RegSource {
    Concrete(u64),
    Symbolic(Sym),
    Uninit,
}

pub fn setup_init_regs<'ir, B: BV, T: Target>(
    shared_state: &SharedState<'ir, B>,
    frame: Frame<'ir, B>,
    checkpoint: Checkpoint<B>,
    regs: Vec<String>,
    register_types: &HashMap<Name, Ty<Name>>,
    init_pc: u64,
    _target: &T,
) -> (Frame<'ir, B>, Checkpoint<B>) {
    let mut local_frame = executor::unfreeze_frame(&frame);
    let ctx = smt::Context::new(smt::Config::new());
    let mut solver = Solver::from_checkpoint(&ctx, checkpoint);
    let mut reg_vars = HashMap::new();

    for reg in regs {
        let ex_var =
            shared_state.symtab.get(&zencode::encode(&reg)).expect(&format!("Register {} missing during setup", reg));
        let ex_val =
            local_frame.regs_mut().get_mut(&ex_var).expect(&format!("No value for register {} during setup", reg));
        match ex_val {
            UVal::Uninit(Ty::Bits(n)) => {
                let var = solver.fresh();
                solver.add(smtlib::Def::DeclareConst(var, smtlib::Ty::BitVec(*n)));
                *ex_val = UVal::Init(Val::Symbolic(var));
                reg_vars.insert(reg, var);
            }
            UVal::Init(Val::Symbolic(var)) => {
                reg_vars.insert(reg, *var);
            }
            UVal::Init(Val::Bits(bits)) => {
                let var = solver.fresh();
                solver.add(smtlib::Def::DeclareConst(var, smtlib::Ty::BitVec(bits.len())));
                *ex_val = UVal::Init(Val::Symbolic(var));
                reg_vars.insert(reg, var);
            }
            _ => panic!("Bad value for register {} in setup", reg),
        }
    }

    let pc_id = shared_state.symtab.lookup("z_PC");
    let pc = local_frame.regs_mut().get_mut(&pc_id).unwrap();
    let pc_type = register_types.get(&pc_id).unwrap();
    match pc_type {
        Ty::Bits(n) => *pc = UVal::Init(Val::Bits(B::new(init_pc, *n))),
        _ => panic!("Bad type for PC: {:?}", pc_type),
    };

    let memory = solver.fresh();
    let read_kind_name = shared_state.symtab.get("zRead_ifetch").expect("Read_ifetch missing");
    let (read_kind_pos, read_kind_size) = shared_state.enum_members.get(&read_kind_name).unwrap();
    let read_kind = EnumMember { enum_id: solver.get_enum(*read_kind_size), member: *read_kind_pos };
    let memory_info: Box<dyn isla_lib::memory::MemoryCallbacks<B>> =
        Box::new(SeqMemory { read_ifetch: read_kind, memory_var: memory });
    local_frame.memory_mut().set_client_info(memory_info);

    solver.add(smtlib::Def::DeclareConst(
        memory,
        smtlib::Ty::Array(Box::new(smtlib::Ty::BitVec(64)), Box::new(smtlib::Ty::BitVec(8))),
    ));

    T::init(shared_state, &mut local_frame, &mut solver, init_pc, reg_vars);

    (freeze_frame(&local_frame), smt::checkpoint(&mut solver))
}

pub fn regs_for_state<'ir, B: BV>(shared_state: &SharedState<'ir, B>, frame: Frame<'ir, B>) -> Vec<(String, RegSource)> {
    let mut local_frame = executor::unfreeze_frame(&frame);
    let mut regs: Vec<String> = (0..31).map(|r| format!("R{}", r)).collect();
    let mut other_regs = ["SP_EL0", "SP_EL1", "SP_EL2", "SP_EL3"].iter().map(|r| r.to_string()).collect();
    regs.append(&mut other_regs);

    let mut reg_sources = vec![];
    for reg in regs {
        let ex_var =
            shared_state.symtab.get(&zencode::encode(&reg)).expect(&format!("Register {} missing during setup", reg));
        let ex_val =
            local_frame.regs_mut().get_mut(&ex_var).expect(&format!("No value for register {} during setup", reg));
        match ex_val {
            UVal::Uninit(Ty::Bits(64)) => {
                reg_sources.push((reg, RegSource::Uninit));
            }
            UVal::Init(Val::Symbolic(var)) => {
                reg_sources.push((reg, RegSource::Symbolic(*var)));
            }
            UVal::Init(Val::Bits(bits)) => {
                let rsrc = RegSource::Concrete(bits.try_into().expect(&format!("Value {} for register {} too large", bits, reg)));
                reg_sources.push((reg, rsrc));
            }
            _ => panic!("Bad value for register {} in setup", reg),
        }
    }
    reg_sources
}

pub fn init_model<'ir, B: BV>(
    shared_state: &SharedState<'ir, B>,
    lets: Bindings<'ir, B>,
    regs: Bindings<'ir, B>,
    memory: &Memory<B>,
) -> (Frame<'ir, B>, Checkpoint<B>) {
    eprintln!("Initialising model...");

    let init_fn = shared_state.symtab.lookup("zinit");
    let (init_args, _, init_instrs) = shared_state.functions.get(&init_fn).unwrap();
    let init_result = SegQueue::new();
    let init_task = LocalFrame::new(init_fn, init_args, None, init_instrs)
        .add_lets(&lets)
        .add_regs(&regs)
        .set_memory(memory.clone())
        .task(0);

    executor::start_single(
        init_task,
        &shared_state,
        &init_result,
        &move |_tid, _task_id, result, _shared_state, mut solver, init_result| match result {
            Ok((_, frame)) => {
                init_result.push((freeze_frame(&frame), smt::checkpoint(&mut solver)));
            }
            Err(err) => eprintln!("Initialisation failed: {:?}", err),
        },
    );
    if init_result.len() != 1 {
        eprintln!("Expected initialisation to have one path, found {}", init_result.len());
        exit(1);
    }
    let (frame, post_init_checkpoint) = init_result.pop().expect("pop failed");
    eprintln!("...done");

    (frame, post_init_checkpoint)
}

pub fn setup_opcode<B: BV>(
    shared_state: &SharedState<B>,
    frame: &Frame<B>,
    opcode: B,
    opcode_mask: Option<u32>,
    prev_checkpoint: Checkpoint<B>,
) -> (Sym, Checkpoint<B>) {
    use isla_lib::primop::smt_value;
    use isla_lib::smt::smtlib::{Def, Exp, Ty};
    use isla_lib::smt::*;

    let ctx = smt::Context::new(smt::Config::new());
    let mut solver = Solver::from_checkpoint(&ctx, prev_checkpoint);

    let local_frame = executor::unfreeze_frame(frame);

    let pc_id = shared_state.symtab.lookup("z_PC");
    let pc = local_frame.regs().get(&pc_id).unwrap();
    let pc = match pc {
        UVal::Init(val) => val,
        _ => panic!("Uninitialised PC!"),
    };
    // This will add a fake read event, but that shouldn't matter
    let read_kind_name = shared_state.symtab.get("zRead_ifetch").expect("Read_ifetch missing");
    let (read_kind_pos, read_kind_size) = shared_state.enum_members.get(&read_kind_name).unwrap();
    let read_kind = EnumMember { enum_id: solver.get_enum(*read_kind_size), member: *read_kind_pos };
    let read_val = local_frame.memory().read(Val::Enum(read_kind), pc.clone(), Val::I128(4), &mut solver).unwrap();

    let opcode_var = solver.fresh();
    solver.add(Def::DeclareConst(opcode_var, Ty::BitVec(32)));

    // Working with a mask currently requires the model to be
    // sufficiently monomorphic, so prefer using a concrete value if
    // we can.  (Even if the variable bitvector length part of the
    // model is fully determined by the unmasked bits, the executor
    // doesn't attempt to replace them with a concrete value.)
    if let Some(opcode_mask) = opcode_mask {
        solver.add(Def::Assert(Exp::Eq(
            Box::new(Exp::Bvand(Box::new(Exp::Var(opcode_var)), Box::new(Exp::Bits64(opcode_mask as u64, 32)))),
            Box::new(Exp::Bits64(opcode.try_into().unwrap() & opcode_mask as u64, opcode.len())),
        )));
    } else {
        solver
            .add(Def::Assert(Exp::Eq(Box::new(Exp::Var(opcode_var)), Box::new(Exp::Bits64(opcode.try_into().unwrap(), opcode.len())))));
    }
    let read_exp = smt_value(&read_val).unwrap();
    solver.add(Def::Assert(Exp::Eq(Box::new(Exp::Var(opcode_var)), Box::new(read_exp))));

    (opcode_var, checkpoint(&mut solver))
}

pub fn run_model_instruction<'ir, B: BV>(
    model_function: &str,
    num_threads: usize,
    shared_state: &SharedState<'ir, B>,
    frame: &Frame<'ir, B>,
    checkpoint: Checkpoint<B>,
    opcode_var: Sym,
    stop_set: &HashSet<Name>,
    dump_events: bool,
) -> Vec<(Frame<'ir, B>, Checkpoint<B>)> {
    let function_id = shared_state.symtab.lookup(&zencode::encode(model_function));
    let (args, _, instrs) = shared_state.functions.get(&function_id).unwrap();

    let local_frame = executor::unfreeze_frame(frame);

    let mut task = local_frame.new_call(function_id, args, Some(&[Val::Unit]), instrs).task_with_checkpoint(1, checkpoint);
    task.set_stop_functions(stop_set);

    let queue = Arc::new(SegQueue::new());

    let now = Instant::now();
    executor::start_multi(
        num_threads,
        None,
        vec![task],
        &shared_state,
        queue.clone(),
        &move |tid, task_id, result, shared_state, solver, collected| {
            log_from!(tid, log::VERBOSE, "Collecting");
            let mut events = simplify(solver.trace());
            let events: Vec<Event<B>> = events.drain(..).map(|ev| ev.clone()).collect();
            match result {
                Ok((val, frame)) => {
                    if let Some((ex_val, ex_loc)) = frame.get_exception() {
                        let s = ex_val.to_string(&shared_state.symtab);
                        collected.push((Err(format!("Exception thrown: {} at {}", s, ex_loc)), events))
                    } else {
                        match val {
                            Val::Unit => collected
                                .push((postprocess(tid, task_id, frame, shared_state, solver, &events), events)),
                            _ =>
                            // Anything else is an error!
                            {
                                log_from!(tid, log::VERBOSE, format!("Unexpected footprint return value: {:?}", val));
                                collected.push((Err(format!("Unexpected footprint return value: {:?}", val)), events))
                            }
                        }
                    }
                }
                Err((ExecError::Dead, _)) => {
                    log_from!(tid, log::VERBOSE, "dead");
                    collected.push((Err(String::from("dead")), events))
                }
                Err((err, backtrace)) => {
                    log_from!(tid, log::VERBOSE, format!("Error {:?}", err));
                    for (f, pc) in backtrace.iter().rev() {
                        log_from!(tid, log::VERBOSE, format!("  {} @ {}", shared_state.symtab.to_str(*f), pc));
                    }
                    collected.push((Err(format!("Error {:?}", err)), events))
                }
            }
        },
    );

    eprintln!("Execution took: {}ms", now.elapsed().as_millis());

    let mut result = vec![];

    loop {
        match queue.pop() {
            Ok((Ok((new_frame, new_checkpoint)), mut events)) => {
                log!(
                    log::VERBOSE,
                    match get_opcode(new_checkpoint.clone(), opcode_var) {
                        Ok(model_opcode) => format!("Found {:#010x}", model_opcode),
                        Err(msg) => format!("Failed to retrieve opcode: {}", msg),
                    }
                );
                if dump_events {
                    let stdout = std::io::stderr();
                    let mut handle = stdout.lock();
                    let events: Vec<Event<B>> = events.drain(..).rev().collect();
                    write_events(&mut handle, &events, &shared_state.symtab);
                }
                result.push((new_frame, new_checkpoint));
            }

            // Error during execution
            Ok((Err(msg), mut events)) => {
                println!("Failed path {}", msg);
                if dump_events {
                    let stdout = std::io::stderr();
                    let mut handle = stdout.lock();
                    let events: Vec<Event<B>> = events.drain(..).rev().collect();
                    write_events(&mut handle, &events, &shared_state.symtab);
                }
            }
            // Empty queue
            Err(_) => break,
        }
    }
    result
}

// Find a couple of scratch registers for the harness, and add a branch to one
// at the end of the test.
pub fn finalize<B: BV>(
    shared_state: &SharedState<B>,
    frame: &Frame<B>,
    checkpoint: Checkpoint<B>,
) -> (u32, u32, Checkpoint<B>) {
    // Find a couple of unused scratch registers for the harness
    let trace = checkpoint.trace().as_ref().expect("No trace!");
    let mut events = simplify(trace);
    let mut regs: HashSet<u32> = (0..31).collect();
    for event in events.drain(..) {
        match event {
            Event::ReadReg(reg, _, _) | Event::WriteReg(reg, _, _) => {
                let name = shared_state.symtab.to_str(*reg);
                if name.starts_with("zR") {
                    let reg_str = &name[2..];
                    if let Ok(reg_num) = u32::from_str_radix(reg_str, 10) {
                        regs.remove(&reg_num);
                    }
                }
            }
            _ => (),
        }
    }

    let mut reg_iter = regs.iter();
    let entry_register = reg_iter.next().expect("No scratch registers available");
    let exit_register = reg_iter.next().expect("Not enough scratch registers available");

    // Add branch instruction at the end of the sequence
    let opcode: u32 = 0xd61f0000 | (*exit_register << 5); // br exit_register
    let (_, new_checkpoint) = setup_opcode(shared_state, frame, B::from_u32(opcode), None, checkpoint);

    (*entry_register, *exit_register, new_checkpoint)
}
