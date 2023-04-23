type register = {
  name : string;
  bitsize : int;
  number : int;
}

type register_cache = (int * Z.t) list

type connection = {
  fd : Unix.file_descr;
  verbose : bool;
  registers : register list;
  mutable register_cache : register_cache option;
}

type command = {
  buf : Buffer.t;
}

exception CommandError of string
exception ProtocolError of string

let ack = Bytes.of_string "+"

let decompress bytes =
  if Bytes.contains bytes '*' then begin
      let buf = Buffer.create (Bytes.length bytes) in
      let rec continue i =
        match Bytes.index_from_opt bytes i '*' with
        | None -> Buffer.add_subbytes buf bytes i (Bytes.length bytes - i)
        | Some j ->
           if j - i > 1 then begin
               Buffer.add_subbytes buf bytes i (j - i - 1);
               continue (j - 1)
             end else begin
               let l = Char.code (Bytes.get bytes (j + 1)) - 28 in
               Buffer.add_bytes buf (Bytes.make l (Bytes.get bytes i));
               continue (j + 2)
             end
      in
      continue 0;
      Buffer.to_bytes buf
    end else bytes

let read_response con =
  let buf = Bytes.create 1024 in
  let bytes_read = Unix.recv con.fd buf 0 1024 [] in
  if con.verbose then Printf.eprintf "Read %d bytes\n%!" bytes_read;
  if bytes_read = 0 then raise @@ ProtocolError "read_response: connection closed";
  let bytes_read =
    if bytes_read = 1 && Bytes.get buf 0 = '+'
    then Unix.recv con.fd buf 0 1024 []
    else bytes_read
  in
  let start =
    if Bytes.get buf 0 = '+' then 1 else 0
  in
  if Bytes.get buf start <> '$' then raise @@ ProtocolError ("read_response: bad packet start: " ^ Char.escaped (Bytes.get buf start));
  let rec find_end buf bytes_read =
    if bytes_read >= 4 && Bytes.get buf (bytes_read - 3) = '#'
    then buf, bytes_read
    else
      let _ = if con.verbose then Printf.eprintf "Continuing because got %c at end\n%!" (Bytes.get buf (bytes_read - 3)) in
      let buf = if bytes_read = Bytes.length buf then Bytes.extend buf 0 1024 else buf in
      let new_bytes = Unix.recv con.fd buf bytes_read (Bytes.length buf - bytes_read) [] in
      if new_bytes = 0 then raise @@ ProtocolError "read_response: connection closed before end of packet";
      find_end buf (bytes_read + new_bytes)
  in
  let buf, bytes_read = find_end buf bytes_read in
  let checksum = ref 0 in
  for i = start + 1 to bytes_read - 4 do
    checksum := (!checksum + int_of_char (Bytes.get buf i)) mod 256
  done;
  let reported_checksum = Bytes.sub_string buf (bytes_read - 2) 2 in
  if not (try Scanf.sscanf reported_checksum "%x" (fun i -> i = !checksum)
          with _exn -> raise @@ ProtocolError ("Bad checksum in packet: " ^ reported_checksum))
  then raise @@ ProtocolError (Printf.sprintf "Packet checksum mismatch: %02x vs %s" !checksum reported_checksum);
  ignore (Unix.write con.fd ack 0 1);
  let result = Bytes.sub buf (start + 1) (bytes_read - 4 - start) in
  decompress result

let start_command s =
  let buf = Buffer.create 128 in
  Buffer.add_char buf '$';
  Buffer.add_string buf s;
  { buf }

let command_append com str =
  Buffer.add_string com.buf str

let command_append_bytes com bytes =
  Buffer.add_bytes com.buf bytes

let send_command con cmd =
  let open Buffer in
  let open Unix in
  let checksum = ref 0 in
  for i = 1 to Buffer.length cmd.buf - 1 do
    checksum := (!checksum + int_of_char (nth cmd.buf i)) mod 256
  done;
  let suffix = Printf.sprintf "#%02x" !checksum in
  add_string cmd.buf suffix;
  let _ = write con.fd (to_bytes cmd.buf) 0 (length cmd.buf) in
  ()

let ok_or_error context response =
  let response = Bytes.to_string response in
  if String.length response = 3 && response.[0] = 'E'
  then raise @@ CommandError response
  else if response = "OK" then ()
  else raise @@ ProtocolError ("Bad response to " ^ context ^ ": " ^ response)

let bytes_to_hex bytes =
  let size = Bytes.length bytes in
  let hex = Bytes.make (2*size) '0' in
  for i = 0 to size - 1 do
    let byte = Printf.sprintf "%02x" (Bytes.get bytes i |> int_of_char) in
    Bytes.set hex (2*i  ) byte.[0];
    Bytes.set hex (2*i+1) byte.[1]
  done;
  hex

let qxfer con object_name annex =
  let bufsize = 4096 in
  let buf = Buffer.create bufsize in
  let rec continue offset =
    let cmd = Printf.sprintf "qXfer:%s:read:%s:%x,%x" object_name annex offset bufsize in
    send_command con (start_command cmd);
    let response = read_response con in
    let len = Bytes.length response in
    if len = 0 then raise @@ CommandError (Printf.sprintf "Unsupported by stub: %s" cmd);
    match Bytes.get response 0 with
    | 'm' | 'l' as c ->
       if len > 1 then
         Buffer.add_subbytes buf response 1 (len - 1);
       if c = 'm'
       then continue (offset + len - 1)
       else buf
    | 'E' ->
       raise @@ CommandError (Printf.sprintf "Error in response to %s: %s" cmd (Bytes.to_string response))
    | _ ->
       raise @@ ProtocolError (Printf.sprintf "Unexpected response to %s: %s" cmd (Bytes.to_string response))
      
  in Buffer.contents (continue 0)

(* Assumes we can do the whole write in one go - should be true for one cap *)
let qxfer_set con object_name annex bytes =
  let base_cmd = Printf.sprintf "qXfer:%s:write:%s:0:" object_name annex in
  let command = start_command base_cmd in
  let hex = bytes_to_hex bytes in
  command_append_bytes command hex;
  send_command con command;
  let response = read_response con in
  if Bytes.get response 0 == 'E'
  then raise @@ CommandError (Printf.sprintf "Error in response to %s...: %s" base_cmd (Bytes.to_string response))
  else () (* TODO: return bytes written; handle incomplete writes/large writes *)

let check_bytes_or_error context response =
  if Bytes.length response = 3 && Bytes.get response 0 = 'E'
  then raise @@ CommandError (Bytes.to_string response)
  else if Bytes.length response mod 2 = 1
  then raise @@ ProtocolError ("Odd length response to " ^ context)
  else ()

(* TODO: only convert byte order if necessary *)
let hex_to_Z_sub bytes offset len =
  let big_endian =
    String.init (2*len) (fun i -> Bytes.get bytes (2*offset + 2*len - 2 - 2 * (i / 2) + i mod 2))
  in
  Z.of_string_base 16 big_endian

let hex_to_Z bytes =
  let len = Bytes.length bytes in
  len / 2, hex_to_Z_sub bytes 0 (len / 2)

let fill_cache con =
  match con.register_cache with
  | Some cache ->
     cache
  | None ->
     send_command con (start_command "g");
     let response = read_response con in
     check_bytes_or_error "reading registers" response;
     Printf.printf "Filling reg cache using %d hex bytes\n%!" (Bytes.length response);
     let next_reg (i,cache) reg =
       let bytesize = (reg.bitsize + 7) / 8 in
       Printf.printf "Reg %s at offset %d with %d bytes" reg.name i bytesize;
       let value = hex_to_Z_sub response i bytesize in
       Printf.printf " value %s\n%!" (Z.format "%x" value);
       (i + bytesize, (bytesize, value)::cache)
     in
     let _, rcache = List.fold_left next_reg (0,[]) con.registers in
     let cache = List.rev rcache in
     con.register_cache <- Some cache;
     cache

let read_register con i =
  send_command con (start_command (Printf.sprintf "p%x" i));
  let response = read_response con in
  if Bytes.length response == 0 then begin
      List.nth (fill_cache con) i
    end else begin
      check_bytes_or_error "reading register" response;
      hex_to_Z response
    end

let hex_of_Z size value =
  let hex = Bytes.make (2*size) '0' in
  for i = 0 to size-1 do
    let byte = Z.extract value (8*i) 8 in
    let s = Z.format "%02x" byte in
    Bytes.set hex (2*i  ) s.[0];
    Bytes.set hex (2*i+1) s.[1]
  done;
  hex

let bytes_for_bits size =
  if size mod 8 == 0 then size / 8 else 1 + size / 8

let list_nth_update l i v =
  List.mapi (fun j w -> if i == j then v else w) l

let send_all_registers con cache =
  let command = start_command "G" in
  List.iter (fun (size, value) ->
      let hex_value = hex_of_Z size value in
      command_append_bytes command hex_value) cache;
  send_command con command;
  ok_or_error "writing all registers" (read_response con)

let write_register con i size value =
  let hex_value = hex_of_Z (bytes_for_bits size) value in
  let command = start_command (Printf.sprintf "P%x=" i) in
  command_append_bytes command hex_value;
  send_command con command;
  let response = read_response con in
  if Bytes.length response == 0 then begin
      let cache = fill_cache con in
      let cache = list_nth_update cache i (bytes_for_bits size, value) in
      con.register_cache <- Some cache;
      send_all_registers con cache
  end else begin
      con.register_cache <- None;
      ok_or_error "writing register" response
    end

let hex_to_bytes hex_bytes =
  let size = Bytes.length hex_bytes / 2 in
  let bytes = Bytes.create size in
  for i = 0 to size - 1 do
    let byte = Bytes.sub_string hex_bytes (i*2) 2 in
    Bytes.set bytes i (Scanf.sscanf byte "%x" char_of_int)
  done;
  bytes

let read_memory con addr length =
  let addr_s = Z.format "%x" addr in
  let command = start_command (Printf.sprintf "m%s,%x" addr_s length) in
  send_command con command;
  let response = read_response con in
  check_bytes_or_error "reading memory" response;
  hex_to_bytes response

let write_memory con addr bytes =
  let size = Bytes.length bytes in
  let hex = bytes_to_hex bytes in
  let addr_s = Z.format "%x" addr in
  let command = start_command (Printf.sprintf "M%s,%x:" addr_s size) in
  command_append_bytes command hex;
  send_command con command;
  ok_or_error "writing memory" (read_response con)

let cont_nw con cmd addr_opt =
  con.register_cache <- None;
  let command = match addr_opt with
    | None -> cmd
    | Some addr -> Printf.sprintf "%s%s" cmd (Z.format "%x" addr)
  in
  send_command con (start_command command)

let cont con cmd addr_opt =
  cont_nw con cmd addr_opt;
  read_response con

let continue con addr_opt = cont con "c" addr_opt
let continue_no_wait con addr_opt = cont_nw con "c" addr_opt
let step con addr_opt = cont con "s" addr_opt
let kill con =
  send_command con (start_command "k");
  read_response con
let detach con =
  send_command con (start_command "D");
  read_response con

type breakpoint = Software | Hardware | WriteWatch | ReadWatch | AccessWatch

let breakpoint_code = function
  | Software -> "0,"
  | Hardware -> "1,"
  | WriteWatch -> "2,"
  | ReadWatch -> "3,"
  | AccessWatch -> "4,"

let do_breakpoint con start ty addr kind =
  let command = start_command start in
  command_append command (breakpoint_code ty);
  command_append command (Z.format "%x" addr);
  command_append command ",";
  command_append command (Option.value kind ~default:"0");
  send_command con command;
  let response = Bytes.to_string (read_response con) in
  if String.length response = 3 && response.[0] = 'E'
  then raise @@ CommandError response
  else if response = ""
  then raise @@ CommandError "Unsupported breakpoint"
  else if response = "OK"
  then ()
  else raise @@ ProtocolError ("Unexpected response to breakpoint operation: " ^ response)

let insert_breakpoint con ty addr kind = do_breakpoint con "Z" ty addr kind
let remove_breakpoint con ty addr kind = do_breakpoint con "z" ty addr kind

(* This is very lax about XML namespace handling - it basically ignores them *)

let read_regs con =
  try
    let next_regnum = ref 0 in
    let rec file name =
      let content = qxfer con "features" name in
      let open Xmlm in
      let xml_input = make_input ~ns:(fun s -> Some s) (`String (0, content)) in
      let el ((_,tag),attrs) sub =
        let find_attr name = List.find_map (fun ((_,n),v) -> if n = name then Some v else None) attrs in
        if tag = "reg" then
          let number = Option.value ~default:(!next_regnum) (Option.map int_of_string (find_attr "regnum")) in
          next_regnum := number + 1;
          let name = find_attr "name" in
          let bitsize = find_attr "bitsize" in
          match name, bitsize with
          | None, _ -> prerr_endline "Warning: register without name"; []
          | Some name, None -> Printf.eprintf "Warning: register %s has no bitsize" name; []
          | Some name, Some bitsize -> [{ name; bitsize = int_of_string bitsize; number }]
        else if tag = "include" then
          match find_attr "href" with
          | None -> prerr_endline "Warning: include without href"; []
          | Some filename -> file filename
        else
          List.concat sub
      in
      snd (input_doc_tree ~el ~data:(fun _ -> []) xml_input)
    in file "target.xml"
  with Xmlm.Error ((line,col), error) -> begin
      Printf.eprintf "Target features XML parsing error at %d.%d: %s" line col (Xmlm.error_message error);
      exit 1
    end

let connect verbose =
  let open Unix in
  let addr = ADDR_INET (inet_addr_loopback, 1234) in
  let fd = socket PF_INET SOCK_STREAM 0 in
  connect fd addr;
  let con = { fd; verbose; registers = []; register_cache = None } in
  begin  
    match Unix.select [con.fd] [] [] 0.5 with
    | [_], _, _ -> Printf.printf "Initial response: %s\n%!" (read_response con |> Bytes.to_string)
    | _ -> ()
  end;
  send_command con (start_command "qSupported:xmlRegisters=i386");
  let _ = read_response con in
  send_command con (start_command "Hgp0.0");
  let _ = read_response con in
  let registers = read_regs con in
  { con with registers }

let interrupt con =
  if con.verbose then Printf.printf "Interrupting\n%!";
  let _ = Unix.write con.fd (Bytes.of_string "\003") 0 1 in
  ignore (read_response con)

let find_register con regmap name =
  try
    List.find (fun r' -> String.compare r'.name (Regmap.lookup regmap name) == 0) con.registers
  with Not_found -> failwith ("Register " ^ name ^ " not found")
