(*
 * Description : ptree.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

exception Ptree_empty
exception Ptree_notfound

type t = 
		EMPTY
	| LEAF of string
	| NODE of string * t list

val make_leaf : string -> t

val make_node : string -> t list -> t

(* fold is the reduce function for the planar tree type *)
val fold : (string -> 'b list -> 'b) -> t -> 'b
		
val paths : t -> string list list

val find : t -> string -> string list

val tree_print : out_channel -> t -> unit
