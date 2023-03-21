module StringMap = Map.Make(String)

let map_from_list l =
  List.fold_left (fun m (k,v) -> StringMap.add k v m) StringMap.empty l

let lookup map r =
  match StringMap.find_opt r map with
  | None -> r
  | Some r' -> r'

let get_map s =
  match s with
  | "" -> StringMap.empty
  | "x86" ->
     map_from_list
       (("rflags.bits", "eflags")::
          (List.init 31 (fun i -> Printf.sprintf "R%d" i, Printf.sprintf "x%d" i)))
  | "x86-sail" ->
     map_from_list
       (("rflags.bits", "rflags")::
          (List.init 31 (fun i -> Printf.sprintf "R%d" i, Printf.sprintf "x%d" i)))
  | _ ->
     Printf.eprintf "Unknown register map: %s" s;
     exit 1
