(*
 * Description : clk_drivers.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

(** yices expr to buffer string *)
val yices_types_to_string : Clk_model.yices_types -> string

val yices_expr_to_buff : Clk_model.yices_expr -> Buffer.t

val and_yices_exprl_list : Clk_model.yices_expr list -> Clk_model.yices_expr

val yices_declaration_to_buff : Clk_model.ycies_declaration -> Buffer.t

(** print clock model *)


(** is event type *)
val is_event_type : Clk_model.yices_types -> bool

(** sig_types to yices_types *)
val sig_abs_to_yices_abs_types : Sig_abs.base_type -> Sig_abs.declaration list -> Clk_model.yices_types

(** create fresh var *)
val create_fresh_vars : Sig_abs.expression -> string * string

(** create constant symbol *)
val create_const_vars : Clk_model.yices_expr -> string

(** create uninterpreted symbol *)
val create_uninterpreted_vars : Sig_abs.expression -> string -> Clk_model.yices_expr -> Clk_model.yices_expr -> string * string

(** create prevar symbol *)
val create_memorized_vars : string -> string * string

(** translate an expression to: clock formula * value formula * value type * list of constraint formulas * list of new local variable *)
val expr_to_yciesformula : Sig_abs.file_type -> Sig_abs.declaration list -> Sig_abs.declaration list -> Sig_abs.declaration list -> 
	Sig_abs.declaration list -> Sig_abs.declaration list -> Sig_abs.expression -> 
	Clk_model.yices_expr * Clk_model.yices_expr * Clk_model.yices_types * Clk_model.yices_expr list * 
	Clk_model.yices_expr list * (string * Clk_model.yices_types) list

(** translate a statement to ycies formula *)
val statement_to_yciesformula : Sig_abs.file_type -> string -> Sig_abs.declaration list -> Sig_abs.declaration list -> Sig_abs.declaration list -> 
	Sig_abs.declaration list -> Sig_abs.declaration list -> Sig_abs.statement -> 
	Clk_model.yices_expr * (string * Clk_model.yices_types) list

(** translate a process to yicess formula *)
(* val process_to_yciesformula : Sig_abs.file_type -> string -> Sig_abs.declaration list -> Sig_abs.declaration list -> Sig_abs.declaration list -> 
	Sig_abs.declaration list -> Sig_abs.declaration list -> Sig_abs.statement -> 
	Clk_model.yices_expr * (string * Clk_model.yices_types) list *)

(** translate a signal program to yicess formula *)
