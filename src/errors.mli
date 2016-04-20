(*
 * Description : error
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

type debug = bool ref

val set_debug : bool -> unit

val current_debug : unit -> bool

val underline_error : string -> int -> int -> string

val display_error : string -> int -> string -> out_channel -> string -> unit



