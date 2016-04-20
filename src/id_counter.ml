(*
 * Description : id_counter.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

let newvar_id = ref (-1)

let init_newvar_id _ = newvar_id := -1

let get_newvar_id _ = !newvar_id

let set_newvar_id id = newvar_id := id

let next_newvar_id _ = newvar_id := (!newvar_id + 1); !newvar_id

let newunint_id = ref (-1)

let init_newunint_id _ = newunint_id := -1

let get_newunint_id _ = !newunint_id

let set_newunint_id id = newunint_id := id

let next_newunint_id _ = newunint_id := (!newunint_id + 1); !newunint_id

(** counter for new constant in Yices *)
let newconstant_id = ref (-1)

let get_newconstant_id _ = !newconstant_id

let set_newconstant_id id = newconstant_id := id

let next_newconstant_id _ = newconstant_id := (!newconstant_id + 1); !newconstant_id

let init_newconstant_id _ = newconstant_id := -1

let formula_id = ref (-1)

let init_formula_id _ = formula_id := -1

let get_formula_id _ = !formula_id

let set_formula_id id = formula_id := id

let next_formula_id _ = formula_id := (!newvar_id + 1); !formula_id

