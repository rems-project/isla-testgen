open Ast

type run_type =
  | Breakpoint of Gdb.breakpoint
  | SingleStep of int option

let z_of_bytes bytes =
  let open Z in
  let twofivesix = Z.of_int 256 in
  Bytes.fold_right (fun b z -> twofivesix*z + Z.of_int (Char.code b)) bytes Z.zero

let bytes_of_z size z =
  Bytes.init size (fun i ->
      Char.chr (Z.to_int (Z.extract z (8*i) 8)))

let send_tagged_memory con addr size z tag =
  let bytes =
    Bytes.init (size + 1) (fun i ->
        if i = 0 then (if tag then '\001' else '\000') else
          Char.chr (Z.to_int (Z.extract z (8*(i-1)) 8)))
  in Gdb.qxfer_set con "capa" (Z.format "%x" addr) bytes

let setup verbose regmap con regs test =
  let set = function
    | Register r ->
       let reg_number =
         try
           List.assoc (Regmap.lookup regmap r.name) regs
         with Not_found -> failwith ("Register " ^ r.name ^ " not found")
       in
       if verbose then Printf.printf "Writing register %s with %s (%d bits)\n%!" r.name (Z.format "#x" r.value) r.size;
       Gdb.write_register con reg_number r.size r.value
    | Memory m ->
       if m.size mod 8 <> 0 then failwith "Memory access not in bytes";
       if verbose then Printf.printf "Writing %s (%d bits) to %s\n%!" (Z.format "#x" m.value) m.size (Z.format "#x" m.address);
       begin match m.tag with
       | None -> Gdb.write_memory con m.address (bytes_of_z (m.size / 8) m.value)
       | Some tag -> send_tagged_memory con m.address (m.size / 8) m.value tag
       end
    | Tag _ ->
       failwith "tag only valid in post-state for now"
  in
  List.iter set test.prestate

let run_test verbose run_type regmap con regs test =
  setup verbose regmap con regs test;
  let execute () =
    match run_type with
    | Breakpoint bp_type -> begin
        let stop =
          match test.run.stop with
          | Some stop -> stop
          | None -> failwith "No stop location in test (necessary in breakpoint mode)"
        in
        if verbose then Printf.printf "Setting breakpoint at %s\n%!" (Z.format "#x" stop);
        Gdb.insert_breakpoint con bp_type stop None;
        if verbose then Printf.printf "Running from %s\n%!" (Option.fold ~none:"current pc" ~some:(Z.format "#x") test.run.start);
        let _ = Gdb.continue con test.run.start in ()
      end
    | SingleStep steps ->
       let steps =
         match steps, test.run.steps with
         | Some s, _ -> s
         | None, Some s -> s
         | None, None -> failwith "Number of steps not given (necessary in single step mode)"
       in
       let _ = Gdb.step con test.run.start in
       for _ = 1 to steps-1 do
         ignore (Gdb.step con None)
       done
  in execute ();
  let check = function
    | Register r ->
       let reg_number =
         try
           List.assoc (Regmap.lookup regmap r.name) regs
         with Not_found -> failwith ("Register " ^ r.name ^ " not found")
       in
       if verbose then Printf.printf "Checking %s\n%!" r.name;
       let expected_bytes = if r.size mod 8 == 0 then r.size / 8 else 1 + r.size / 8 in
       let (sz,v) = Gdb.read_register con reg_number in
       if sz <> expected_bytes then failwith (Printf.sprintf "Bytes receieved for register %s mismatch: %d received, %d expected" r.name (sz * 8) expected_bytes);
       if Z.compare r.value v == 0
       then None
       else Some (Printf.sprintf "Register %s mismatch: %s received, %s expected" r.name (Z.format "#x" v) (Z.format "#x" r.value))
    | Memory m ->
       if m.size mod 8 <> 0 then failwith "Memory access not in bytes";
       if verbose then Printf.printf "Checking %s\n%!" (Z.format "#x" m.address);
       let bytes = Gdb.read_memory con m.address (m.size / 8) in
       let v = z_of_bytes bytes in
       if Z.compare m.value v == 0
       then None
       else Some (Printf.sprintf "Memory mismatch at %s: received %s, expected %s in %d bits" (Z.format "#x" m.address) (Z.format "#x" v) (Z.format "#x" m.value) m.size)
    | Tag t ->
       if verbose then Printf.printf "Checking tag at %s\n%!" (Z.format "#x" t.address);
       let bytes = Gdb.qxfer con "capa" (Z.format "%x" t.address) in
       let tag = match bytes.[0], bytes.[1] with
         | '0', '0' -> false
         | '0', '1' -> true
         | _ -> failwith "Bad tag value"
       in
       if tag = t.tag then None
       else Some (Printf.sprintf "Tag mismatch at %s: received %B, expected %B" (Z.format "#x" t.address) tag t.tag)
  in
  match List.filter_map check test.poststate with
  | [] -> (print_endline "OK"; 0)
  | fails ->
     print_endline "FAIL";
     List.iter print_endline fails;
     1

