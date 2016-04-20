(*
 * Description : error
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

(** default debug = false *)
type debug = bool ref

let debug = ref false

let set_debug b = debug := b

let current_debug () = !debug
 
let underline_error buffer start stop =
	let len = String.length buffer in
	let start' = max 0 start in
	let stop' = max 1 stop in
	(
		(if start' > 0 then (String.sub buffer 0 start') else "")
		^ "\027[4m"
		^ (if (stop' - start') <> 0
			then (String.sub buffer start' (stop' - start' ) )
			else ""
		)
		^ "\027[0m"
		^ (if stop' < len then (String.sub buffer stop' (len - stop') ) else "")
	)
	
let display_error filename lineno line oc msg =
	output_string (oc) (
			(filename) ^ "["
			^ (string_of_int (lineno)) ^ "] "
		^ msg ^ " \n"
	);
	flush (oc)