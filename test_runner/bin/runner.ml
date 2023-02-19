open Test_runner

let usage = "test_runner <test file>"

let test_file = ref (None : string option)
let run_type = ref (Runner.Breakpoint Gdb.Hardware)
let verbose = ref false
let gdb_verbose = ref false
let wait_for_breakpoint = ref false
let kill = ref false

let options = [
    ("--single-step", Arg.Unit (fun _ -> run_type := Runner.SingleStep None), "Run in single step mode");
    ("--single-step-for", Arg.Int (fun i -> run_type := Runner.SingleStep (Some i)), "Run in single step mode for n steps");
    ("--verbose", Arg.Set verbose, "Print more information");
    ("--gdb-verbose", Arg.Set gdb_verbose, "Print GDB protocol information");
    ("--sw-breakpoint", Arg.Unit (fun _ -> run_type := Runner.Breakpoint Gdb.Software), "Use a software breakpoint");
    ("--wait-for-breakpoint", Arg.Set wait_for_breakpoint, "Run the processor until it hits a breakpoint before running test");
    ("--kill", Arg.Set kill, "Send a kill request at the end of the test");
  ]
let anon_arg s =
  match !test_file with
  | None -> test_file := Some s
  | Some _ -> raise (Arg.Bad "Multiple test file arguments given")

let () = Arg.parse options anon_arg usage

let test_file =
  match !test_file with
  | None ->
     prerr_endline "No script file given";
     Arg.usage options usage;
     exit 1
  | Some s -> s

let script = Parser.read_test test_file
let con = Gdb.connect !gdb_verbose;;
let regs = Readregs.read_regs con;;
if !wait_for_breakpoint then ignore (Gdb.continue con None);;
Runner.run_test !verbose !run_type con regs script;;
if !kill then ignore (Gdb.kill con);;
