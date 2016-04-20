(*
 * Description : input_handle.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
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

let current_handle = ref {
		h_line = "";
		h_lineno = 0;
		h_pos = 0;
		h_out_channel = stderr;
		h_file = (SOURCE_CODE,"");
}

let line h = h.h_line
let lineno h = h.h_lineno
let pos h = h.h_pos
let real_pos i h = i - h.h_pos
let out_channel h = h.h_out_channel
let file_name h = let (ftype,fname) = h.h_file in fname
let file_type h = let (ftype,fname) = h.h_file in ftype

let curline () = (!current_handle).h_line
let curlineno () = (!current_handle).h_lineno
let curpos () = (!current_handle).h_pos
let curoutchannel () = (!current_handle).h_out_channel
let curfile () = let (ftype,fname) = (!current_handle).h_file in fname
let curtype () = let (ftype,fname) = (!current_handle).h_file in ftype

(*
 * Buffer processor
 *)  	
let set_lineno num =
	(!current_handle).h_lineno <- num

let set_line str = 
	(!current_handle).h_line <- str
	
let set_pos pos = 
	(!current_handle).h_pos <- pos

let set_name name =
	(!current_handle).h_file <- ((curtype ()),name)

let set_type ftype = 
	(!current_handle).h_file <- (ftype,(curfile ()))

(* init: handle -> ()
 * Initialize lexer.
 *)
let init hdl =
	current_handle := hdl
