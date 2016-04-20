(*
 * Description : clk_model.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

(*
 * Description a subset of the Yices input language, including
 * declarations, types, expressions, commands
 *
 *)

(** basic types *)
type yices_types = 
		Y_NOTYPE
	|	Y_BOOL
	| Y_NAT
	| Y_INT
	| Y_REAL
	| Y_NAMED_TYPED of string
	| Y_CONST of yices_types
	| Y_FUNC of yices_types list * yices_types (** name, domain list, and range *)
	| Y_TUPLE of yices_types list (** name, and types *)
	| Y_RECORD of string * (string * yices_types) list (** name, fields list *)
	| Y_SCALAR of string * string list (** name, values *)
	| Y_COMPLEX (** tuple of two reals *)
	| Y_ARRAY of yices_types (** function from int to value type *)

(** declarations *)
and yices_name = string * yices_expr

(** declarations of type and variable *)
and ycies_declaration =
		Y_TYPEDEF of yices_types * string 
	| Y_VARDEF	of yices_types * yices_name

and logcial_context = {
		ycies_typedefs : ycies_declaration list;
		ycies_variables : ycies_declaration list;
		ycies_formulas : yices_expr list;
	}

(** expressions *)
and yices_expr = 
		Y_NOTHING
		(** variable *)
	| Y_VAR of string
		(** constants *)
	| Y_CTRUE
	| Y_CFALSE
	| Y_CNAT of string
	|	Y_CINT of string
	| Y_CREAL of string
	| Y_CCOMPLEX of string * string
	| Y_CCHAR of string
	| Y_CSTRING of string
	| Y_ABSENCE of yices_types
	  (** boolean *)
	| Y_AND of yices_expr list
	| Y_OR of yices_expr list
	| Y_NOT of yices_expr
	| Y_IMPLY of yices_expr * yices_expr
		(** equality *)
	| Y_EQ of yices_expr * yices_expr
	| Y_DIFF of yices_expr * yices_expr
		(** quantifier *)
	| Y_FORALL of (string * yices_types) list * yices_expr
	| Y_EXIST of (string * yices_types) list * yices_expr
		(** arithmetic *)
	| Y_ADD of yices_expr * yices_expr
	| Y_MINUS of yices_expr * yices_expr
	| Y_MULT of yices_expr * yices_expr
	| Y_DIV of yices_expr * yices_expr
	| Y_INTDIV of yices_expr * yices_expr
	| Y_MOD of yices_expr * yices_expr
	| Y_LT of yices_expr * yices_expr
	| Y_LTE of yices_expr * yices_expr
	| Y_GT of yices_expr * yices_expr
	| Y_GTE of yices_expr * yices_expr
		(** others *)
	| Y_FUNCALL of string * yices_expr list (** function name and argument list *)
	| Y_MKTUPLE of yices_expr list (** make a tuple *)
	| Y_SELECT_TUPLE of yices_expr * yices_expr (** tuple variable name and index *)
	| Y_UPDATE_TUPLE of yices_expr * yices_expr * yices_expr
	| Y_MKRECORD of (string * yices_expr) list
	| Y_SELECT_RECORD of yices_expr * yices_expr (** record variable name and field name *)
	| Y_UPDATE_RECORD of yices_expr * yices_expr * yices_expr
