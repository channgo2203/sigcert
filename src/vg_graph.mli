(*
 * Description : Value-Graph implementation.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>

 * This module builds a shared value-graph from 
 * abstract syntax representation of programs 
 * based on a set of rewrite rules.
 *)

(* value-graph data-structe consists of:
 * + status information
 * + a map from vertex (int) to data and the list of adjacences
 * + a map from data to vertex (int)
 * for every kind of expression, it's good idea to define a constructor
 *)

open Vg_types

(** counter for node_id *) 
val node_id : int ref
val node_reset : unit -> unit
val get_node_id : unit -> int
val set_node_id : int -> unit
val next_node_id : unit -> int

(** init an empty value-graph *)
val vg_init : unit -> value_graph
(** add a value to graph *)
val vg_add_value : value_graph -> vg_value -> value_graph
(** transform a value-graph into a new value-graph *)

