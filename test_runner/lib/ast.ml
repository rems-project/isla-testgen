(* No CHERI yet *)

(* Sizes are in bits, in particular because registers might not be
   made up of bytes. *)
type requirement =
  | Register of { name: string; size: int; value: Z.t }
  | Memory of { address: Z.t; size: int; value: Z.t; tag: bool option }
  | Tag of { address: Z.t; tag: bool }

type run = {
    start: Z.t option;
    stop: Z.t option;
    steps: int option;
}

type test = {
    prestate: requirement list;
    run: run;
    poststate: requirement list;
}
