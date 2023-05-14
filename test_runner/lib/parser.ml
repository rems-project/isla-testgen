open Ast

let rec strip_comments = function
  | [] -> []
  | "//"::_ -> []
  | h::t -> h::(strip_comments t)

let read_test filename =
  let channel = open_in filename in
  let read_reqs end_token =
    let reqs = ref [] in
    let rec read_req_aux () =
      let line = input_line channel in
      let tokens = String.split_on_char ' ' line in
      match strip_comments tokens with
      | "reg"::name::size::value::t ->
         let size = match int_of_string_opt size with
           | None -> failwith ("Bad size in register requirement: " ^ size)
           | Some i -> i
         in
         let value = match Z.of_string value with
           | v -> v
           | exception Invalid_argument _ -> failwith ("Bad value in register requirement: " ^ value)
         in
         let mask = match t with
           | [] -> None
           | ["mask"; v] ->
              begin
                match Z.of_string v with
                | v -> Some v
                | exception Invalid_argument _ -> failwith ("Bad mask in register requirement: " ^ v)
              end
           | _ -> failwith ("Bad register requirement, need 'name size value tag [\"mask\" mask]': " ^ line)
         in
         reqs := Register {name; size; value; mask} :: !reqs;
         read_req_aux ()
      | "reg"::_ -> failwith ("Bad register requirement, need 'name size value tag [\"mask\" mask]': " ^ line)
      | "mem"::address::size::value::tl ->
         let address = match Z.of_string address with
           | v -> v
           | exception Invalid_argument _ -> failwith ("Bad address in register requirement: " ^ address)
         in
         let size = match int_of_string_opt size with
           | None -> failwith ("Bad size in register requirement: " ^ size)
           | Some i -> i
         in
         let value = match Z.of_string value with
           | v -> v
           | exception Invalid_argument _ -> failwith ("Bad value in register requirement: " ^ value)
         in
         let tag = match tl with
           | [] -> None
           | "t"::_ -> Some true
           | "f"::_ -> Some false
           | h::_ -> failwith ("Bad tag in mem: " ^ h)
         in
         reqs := Memory {address; size; value; tag} :: !reqs;
         read_req_aux ()
      | ["tag"; address; tag] ->
         let address = match Z.of_string address with
           | v -> v
           | exception Invalid_argument _ -> failwith ("Bad address in register requirement: " ^ address)
         in
         let tag = match tag with
           | "t" -> true
           | "f" -> false
           | _ -> failwith ("Bad tag in tag: " ^ tag)
         in
         reqs := Tag { address; tag } :: !reqs;
         read_req_aux ()

      | s::t when s = end_token -> List.rev !reqs, t
      | _ -> failwith ("Bad requirement line: " ^ line)
    in read_req_aux ()
  in
  let decode_run =
    let rec aux run = function
    | [] -> run
    | "start"::start::t -> begin
        if Option.is_some run.start then failwith "Multiple start locations";
        match Z.of_string start with
        | start -> aux {run with start = Some start} t
        | exception Invalid_argument _  -> failwith ("Bad start location: " ^ start)
      end
    | "stop"::stop::t -> begin
        if Option.is_some run.stop then failwith "Multiple stop locations";
        match Z.of_string stop with
        | stop -> aux {run with stop = Some stop} t
        | exception Invalid_argument _ -> failwith ("Bad stop location: " ^ stop)
      end
    | "steps"::steps::t -> begin
        if Option.is_some run.steps then failwith "Multiple steps parameters";
        match int_of_string_opt steps with
        | None -> failwith ("Bad steps location: " ^ steps)
        | Some steps -> aux {run with steps = Some steps} t
      end
    | bad::_ -> failwith ("Bad run parameter: " ^ bad)
    in aux {start = None; stop = None; steps = None}
  in   
  let prestate, run = read_reqs "RUN" in
  let run = decode_run run in
  let poststate, _ = read_reqs "END" in
  close_in channel;
  { prestate; run; poststate }
