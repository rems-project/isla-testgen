open Gdb
open Readregs

module type TEST = sig
  val con : connection
  val simple_command : string -> Bytes.t
  val regs : (string * int) list
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
     let regs = read_regs con
   end)
