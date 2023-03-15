(* This is very lax about XML namespace handling - it basically ignores them *)

let read_regs con =
  try
    let next_regnum = ref 0 in
    let rec file name =
      let content = Gdb.qxfer con "features" name in
      let open Xmlm in
      let xml_input = make_input ~ns:(fun s -> Some s) (`String (0, content)) in
      let el ((_,tag),attrs) sub =
        let find_attr name = List.find_map (fun ((_,n),v) -> if n = name then Some v else None) attrs in
        if tag = "reg" then
          let num = Option.value ~default:(!next_regnum) (Option.map int_of_string (find_attr "regnum")) in
          next_regnum := num + 1;
          let name = find_attr "name" in
          match name with
          | None -> prerr_endline "Warning: register without name"; []
          | Some n -> [(n,num)]
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
