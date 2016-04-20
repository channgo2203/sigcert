(*
  Description : Value-Graph implementation.
  Copyright   : (c) Chan Ngo 2013
  License     : All Rights Reserved
  Maintainer  : Chan Ngo <chan.ngo@inria.fr>

  This module builds a shared value-graph from 
	abstract syntax representation of programs 
	based on a set of rewrite rules.
*)

open Exceptions
open Vg_types

(** counter for node_id *)
let node_id = ref (-1)
let node_reset () = node_id := -1
let get_node_id () = !node_id
let set_node_id id = node_id := id
let next_node_id () = node_id := !node_id + 1; !node_id

(** init an empty value-graph *)
let vg_init () = 
	let _ = node_reset () in
	{
		empty = true;
		keymap = IntMap.empty;
		valuemap = ValueMap.empty;
		nodehash = (Hashtbl.create 10:(int,vg_node)Hashtbl.t)
	}

(** add a value to graph *)
let rec vg_add vg value = 
	let new_node_id = next_node_id () in 
	let new_keymap = IntMap.add new_node_id value vg.keymap in
	let new_valuemap = ValueMap.add value new_node_id vg.valuemap in
	(* recursively add sub-value *)

	{
		empty = false;
		keymap = new_keymap;
		valuemap = new_valuemap;
		nodehash = vg.nodehash
	}
		
let vg_add_value vg value =
	(* check whether the value already exists *)
	if ((ValueMap.mem value vg.valuemap)) then vg
	else
		begin
			vg
		end
