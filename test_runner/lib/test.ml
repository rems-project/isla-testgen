open Gdb

(*

dune top
<copy into ocaml toplevel>

open Test_runner;;
module T = (val Test.make ());;
open T;;

 *)

module type TEST = sig
  val con : connection
  val simple_command : string -> Bytes.t
  val read_reg : string -> int * string
end

let make () : (module TEST) =
  let con = connect true in
  begin  
    match Unix.select [con.fd] [] [] 0.5 with
    | [_], _, _ -> Printf.printf "Initial repsonse: %s\n%!" (read_response con |> Bytes.to_string)
    | _ -> ()
  end;
  let simple_command s =
    send_command con (start_command s);
    read_response con
  in
  (module struct
     let con = con
     let simple_command = simple_command
     let read_reg r =
       let reg = Gdb.find_register con Regmap.StringMap.empty r in
       let sz,v = Gdb.read_register con reg.Gdb.number in
       sz, Z.format "%x" v
   end)
