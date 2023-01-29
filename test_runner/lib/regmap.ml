module StringMap = Map.Make(String)

let map_from_list l =
  List.fold_left (fun m (k,v) -> StringMap.add k v m) StringMap.empty l

let lookup map r =
  match StringMap.find_opt r map with
  | None -> r
  | Some r' -> r'

let map =
  map_from_list
    (List.init 31 (fun i -> Printf.sprintf "R%d" i, Printf.sprintf "x%d" i))
