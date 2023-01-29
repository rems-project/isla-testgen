type connection = { fd : Unix.file_descr; verbose : bool }
type command

exception CommandError of string
exception ProtocolError of string

(** [connect verbose] *)
val connect : bool -> connection

val start_command : string -> command
val command_append : command -> string -> unit
val command_append_bytes : command -> bytes -> unit
val send_command : connection -> command -> unit
val read_response : connection -> bytes
val check_bytes_or_error : string -> bytes -> unit

val qxfer : connection -> string -> string -> string

(** [read_register con i] will read register number [i], returning the size in bits *)
val read_register : connection -> int -> int * Z.t

(** [write_register con i size value] will attempt to write register [i]
    with [value] of [size]. *)
val write_register : connection -> int -> int -> Z.t -> unit

val hex_to_Z : bytes -> int * Z.t
val hex_of_Z : int -> Z.t -> bytes

(** [read_memory con address size] will read [size] bytes from [address]. *)
val read_memory : connection -> Z.t -> int -> bytes

(** [write_memory con address bytes] will write [bytes] to [address]. *)
val write_memory : connection -> Z.t -> bytes -> unit

(** Continue execution at current PC, or the given address. TODO: blocking? *)
val continue : connection -> Z.t option -> bytes

(** Execute a single step at the current PC, or the given address. *)
val step : connection -> Z.t option -> bytes

type breakpoint = Software | Hardware | WriteWatch | ReadWatch | AccessWatch

val insert_breakpoint :
  connection -> breakpoint -> Z.t -> string option -> unit
val remove_breakpoint :
  connection -> breakpoint -> Z.t -> string option -> unit
