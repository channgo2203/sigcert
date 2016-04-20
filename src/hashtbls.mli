(*
 * Description : hashtbls.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)


(** hash of new fresh local vars *)
val add_freshvar_hashtbl : Sig_abs.expression -> string -> unit
val get_freshvar_hashtbl : Sig_abs.expression -> string
(** hash of uninterpreted functions *)
val add_unint_hashtbl : Sig_abs.expression -> string -> unit
val get_unint_hashtbl : Sig_abs.expression -> string
val add_val_unint_hashtbl : string -> (string * Clk_model.yices_expr * Clk_model.yices_expr) -> unit
val get_val_unint_hashtbl : string -> (string * Clk_model.yices_expr * Clk_model.yices_expr)
(** hash of constants *)
val add_const_hashtbl : Clk_model.yices_expr-> string -> unit
val get_const_hashtbl : Clk_model.yices_expr -> string
val add_val_const_hashtbl : string -> Clk_model.yices_expr -> unit
val get_val_const_hashtbl : string -> Clk_model.yices_expr
(** hash of pre_value *)
val add_prevar_hashtbl : string -> string -> unit
val get_prevar_hashtbl : string -> string

(** clock model: hash for typedefs, variables, fromulas *)
val add_yices_type_hashtbl : int -> Clk_model.ycies_declaration -> unit
val get_yices_type_hashtbl : int -> Clk_model.ycies_declaration
val add_yices_var_hashtbl : int -> Clk_model.ycies_declaration -> unit
val get_yices_var_hashtbl : int -> Clk_model.ycies_declaration
val add_source_yices_formula_hashtbl : int -> Clk_model.yices_expr -> unit
val get_source_yices_formula_hashtbl : int -> Clk_model.yices_expr
val add_cmp_yices_formula_hashtbl : int -> Clk_model.yices_expr -> unit
val get_cmp_yices_formula_hashtbl : int -> Clk_model.yices_expr 

