open Test_runner

let file = Sys.argv.(1);;
let con = Gdb.connect false;;
let content = Gdb.qxfer con "features" file;;
print_endline content;;
