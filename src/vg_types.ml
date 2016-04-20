(*
  Description : Value-Graph implementation.
  Copyright   : (c) Chan Ngo 2013
  License     : All Rights Reserved
  Maintainer  : Chan Ngo <chan.ngo@inria.fr>

  This module builds a shared value-graph from 
	abstract syntax representation of programs 
	based on a set of rewrite rules.
*)

(** node value type *)
type vg_node_value_type =
	| VG_NODE_ABSENCE
	| VG_NODE_CLK
	| VG_NODE_VALUE
	| VG_NODE_SIGNAL
	| VG_NODE_NONDETER 

(** node type *)
type vg_node_type =
	| VG_NODE_INPUT of vg_node_value_type
	| VG_NODE_OUTPUT of vg_node_value_type
	| VG_NODE_LOCAL of vg_node_value_type

(** label of a node *) 
type vg_label = 
	| VG_NONE
	| VG_LABEL of string list

(** a node *)
type vg_node = 
	{
		node_type : vg_node_type;
		node_label : vg_label;
	}
	
(** varible type *)
type vg_type =
	| VG_T_BOOL
	| VG_T_INT
	| VG_T_REAL
	| VG_T_COMPLEX
	| VG_T_CHAR
	| VG_T_STRING
	| VG_T_EXTERNALTYPE of string
  | VG_T_ENUM of string * string list (* enum name and value *)
	| VG_T_ARRAY of string * vg_type * int (* array name, type and size *)
	| VG_T_PHINODE of vg_type (* phi-node with type of two branches *)
  | VG_T_UNDET
	
(** a value of a vertex is:
	  + constant
		+ variable (previous value, clock, signal)
		+ unary operator
		+ binary operator
		+ gated phi node
		+ process invocation
		+ enum, array, bundle, struct
 *)
and vg_value = 
	(* constants *)
	| VG_CBOOL of vg_type * bool
	| VG_CINT of vg_type * int
	| VG_CREAL of vg_type * float
	| VG_CCHAR of vg_type * char
	| VG_CSTRING of vg_type * string
	(* enumerator, array, bundle, struct *)
	| VG_CENUMREF of vg_type * vg_value
	(* variable *)
	| VG_VAR of vg_type * string 
	(* conversions *)
	| VG_CONVERSION of vg_type * vg_type * vg_value (* new type, orignal type and value *)
	(* boolean expressions *)
	| VG_NOT of vg_type * vg_value 
	| VG_OR of vg_type * vg_value * vg_value
  | VG_AND of vg_type * vg_value * vg_value
  | VG_XOR of vg_type * vg_value * vg_value
	(* boolean realtions *)
	| VG_EQ of vg_type * vg_value * vg_value
	| VG_DIFF of vg_type * vg_value * vg_value
	| VG_GT of vg_type * vg_value * vg_value
	| VG_GTE of vg_type * vg_value * vg_value 
  | VG_LT of vg_type * vg_value * vg_value
  | VG_LTE of vg_type * vg_value * vg_value 
	(* arithmetic expressions *)
	| VG_PLUS of vg_type * vg_value * vg_value
	| VG_MINUS of vg_type * vg_value * vg_value
	| VG_MULT of vg_type * vg_value * vg_value
	| VG_DIV of vg_type * vg_value * vg_value
	| VG_MODULO of vg_type * vg_value * vg_value
	| VG_POWER of vg_type * vg_value * vg_value
	| VG_COMPLEXDENOTE of vg_type * vg_value * vg_value
	(* unary operators *)
	| VG_UMINUS of vg_type * vg_value
	(* gated phi node *)
	| VG_GPHI of vg_type * vg_value * vg_value * vg_value

(** value-graph
 *  keymap: a map from node_id to value
 * 	valuemap: a map from value to node_id
 *  nodehash: a hash table from node_id to node
 *)
module IntMap = Map.Make(struct type t = int let compare : int -> int -> int = compare end)

module ValueMap = Map.Make(struct type t = vg_value let compare : vg_value -> vg_value -> int = compare end)

type value_graph = 
	{
		empty : bool;
		keymap : vg_value IntMap.t;
		valuemap : int ValueMap.t;
		nodehash : (int,vg_node)Hashtbl.t;
	}
