(*
 * Description : hashtbls.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

open Exceptions

let safe_find ht x s = 
  try
    Hashtbl.find ht x
  with  Not_found -> 
    raise (SymNotFound s)

(** hash of new fresh local vars *)
let freshvar_hashtbl = (Hashtbl.create 10:(Sig_abs.expression,string)Hashtbl.t)
let add_freshvar_hashtbl = Hashtbl.replace freshvar_hashtbl
let get_freshvar_hashtbl expr = safe_find freshvar_hashtbl expr "get_freshvar_symbol"

(** hash of uninterpreted functions *)
let unint_hashtbl = (Hashtbl.create 10:(Sig_abs.expression,string)Hashtbl.t)
let add_unint_hashtbl = Hashtbl.replace unint_hashtbl
let get_unint_hashtbl expr = safe_find unint_hashtbl expr "get_unint_symbol"
let val_unint_hashtbl = (Hashtbl.create 10:(string,(string * Clk_model.yices_expr * Clk_model.yices_expr))Hashtbl.t)
let add_val_unint_hashtbl = Hashtbl.replace val_unint_hashtbl
let get_val_unint_hashtbl str = safe_find val_unint_hashtbl str "get_val_unint_symbol"

(** hash of constants *)
let const_hashtbl = (Hashtbl.create 10:(Clk_model.yices_expr,string)Hashtbl.t)
let add_const_hashtbl = Hashtbl.replace const_hashtbl
let get_const_hashtbl expr = safe_find const_hashtbl expr "get_const_symbol"
let val_const_hashtbl = (Hashtbl.create 10:(string,Clk_model.yices_expr)Hashtbl.t)
let add_val_const_hashtbl = Hashtbl.replace val_const_hashtbl
let get_val_const_hashtbl str = safe_find val_const_hashtbl str "get_const_symbol"

(** hash of pre_va *)
let prevar_hashtbl = (Hashtbl.create 10:(string,string)Hashtbl.t)
let add_prevar_hashtbl = Hashtbl.replace prevar_hashtbl
let get_prevar_hashtbl str = safe_find prevar_hashtbl str "get_prevar_symbol"

(** clock model: hash for typedefs, variables, fromulas *)
let yices_type_hashtbl = (Hashtbl.create 10:(int,Clk_model.ycies_declaration)Hashtbl.t)
let add_yices_type_hashtbl = Hashtbl.replace yices_type_hashtbl
let get_yices_type_hashtbl id = safe_find yices_type_hashtbl id "get_yices_type"
let yices_var_hashtbl = (Hashtbl.create 10:(int,Clk_model.ycies_declaration)Hashtbl.t)
let add_yices_var_hashtbl = Hashtbl.replace yices_var_hashtbl
let get_yices_var_hashtbl id = safe_find yices_var_hashtbl id "get_yices_var"
let source_yices_formula_hashtbl = (Hashtbl.create 10:(int,Clk_model.yices_expr)Hashtbl.t)
let add_source_yices_formula_hashtbl = Hashtbl.replace source_yices_formula_hashtbl
let get_source_yices_formula_hashtbl formula_id = safe_find source_yices_formula_hashtbl formula_id "get_source_yices_formula"
let cmp_yices_formula_hashtbl = (Hashtbl.create 10:(int,Clk_model.yices_expr)Hashtbl.t)
let add_cmp_yices_formula_hashtbl = Hashtbl.replace cmp_yices_formula_hashtbl
let get_cmp_yices_formula_hashtbl formula_id = safe_find cmp_yices_formula_hashtbl formula_id "get_cmp_yices_formula"
