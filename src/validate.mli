(*
 * Description : Validate.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

(* verification of clock *)
val clk_validate : string -> string -> int

(* verification of dependence *)
val dep_validate : string -> string -> int

(* verification of value *)
val equ_validate : string -> string -> int
