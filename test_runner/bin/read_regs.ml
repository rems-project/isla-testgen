open Test_runner
open Gdb

let con = connect false;;
List.iter (fun r -> Printf.printf "%4d %s (%d bits)\n%!" r.number r.name r.bitsize) con.registers
