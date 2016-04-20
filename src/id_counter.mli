(*
 * Description : id_counter.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

(* counter for
 * fresh vars, 
 * uninterpreted functions,
 * constants
 *)

(** counter for new variable in Yices *)
val newvar_id : int ref
val get_newvar_id : 'a -> int
val set_newvar_id : int -> unit
val next_newvar_id : 'a -> int
val init_newvar_id : 'a -> unit

(** counter for new uninterpreted function in Yices *)
val newunint_id : int ref
val get_newunint_id : 'a -> int
val set_newunint_id : int -> unit
val next_newunint_id : 'a -> int
val init_newunint_id : 'a -> unit

(** counter for new constant in Yices *)
val newconstant_id : int ref 
val get_newconstant_id : 'a -> int
val set_newconstant_id : int -> unit
val next_newconstant_id : 'a -> int
val init_newconstant_id : 'a -> unit

(** counter for yices formula id *)
val formula_id : int ref
val get_formula_id : 'a -> int
val set_formula_id : int -> unit
val next_formula_id : 'a -> int
val init_formula_id : 'a -> unit