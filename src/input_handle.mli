(*
 * Description : input_handle.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

(* 
 * Input handle
 *)
type file_type = 
	| SOURCE_CODE
	| COMPILED_CODE

type handle = {
	mutable h_line: string;
	mutable h_lineno: int;
	mutable h_pos: int;
	h_out_channel: out_channel;
	mutable h_file: file_type * string;
}

val current_handle : handle ref

val line : handle -> string

val lineno : handle -> int

val pos : handle -> int

val real_pos : int -> handle -> int

val out_channel : handle -> out_channel

val file_name : handle -> string

val file_type : handle -> file_type

val curline : unit -> string

val curlineno : unit -> int

val curpos : unit -> int 

val curoutchannel : unit -> out_channel

val curfile : unit -> string

val curtype : unit -> file_type

val init : handle -> unit

val set_line : string -> unit

val set_lineno : int -> unit

val set_pos : int -> unit

val set_name : string -> unit

val set_type : file_type -> unit
