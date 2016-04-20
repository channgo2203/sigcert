(*
 * Description : solver_yices.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)


(** clock refinement checking - call the prover *)
val clk_refinement_check : string -> bool

(** dependency refinement checking - call the prover *)
val dep_refinement_check : string -> bool

