(*
 * Description : exceptions.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

(* vg_type.ml *)
exception Vg_Incomparable

(* sig_lexer and sig_parser *)
exception Eof
exception InternalError of string
exception ParseMismatch

(* sig_abs *)
exception BadType
exception BadDefinition

(* Thrown when an unconsistent Signal abstract syntax is found *)
exception UnconsistentDef

(* Variable not found *)
exception VariableNotFound of string

(* Typedef not found *)
exception TypedefNotFound of string

(* Invalid Signal expression *)
exception InvalidExprssion of string

(* Invalid Signal statement *)
exception InvalidStatement of string

(* Symbol not found *)
exception SymNotFound of string 