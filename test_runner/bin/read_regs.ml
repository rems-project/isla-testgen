open Test_runner

let con = Gdb.connect false;;
let regs = Readregs.read_regs con;;
List.iter (fun (s,i) -> Printf.printf "%4d %s\n%!" i s) regs
