(*
 * Description : ptree.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

exception Ptree_empty
exception Ptree_notfound

type t = 
		EMPTY
	| LEAF of string
	| NODE of string * t list


let make_leaf s = LEAF(s)

let make_node s lt = NODE(s,lt)

(* fold function for trees. *)
let rec fold f t =
	match t with
	| EMPTY -> raise Ptree_empty
	| LEAF(s) -> f s []
	| NODE(s,lst) -> f s (List.map (fold f) lst)

(* get all paths from root *)
let paths t =
	fold (fun s lst -> match lst with 
	| [] -> [ [s] ]
  | y :: ys -> List.fold_left ( @ ) [[s]]
               (List.map (fun a -> List.map (fun b -> s :: b) a) lst) ) t

(* find a node and return a list of nodes backward to the root *)
let find t nodename =
	List.tl (List.rev (List.find (List.mem nodename) (paths t)))
	
(* print a process tree to output channel *)
let rec tree_print oc t =
	match t with
	| EMPTY -> Printf.fprintf oc "*Empty*"
	| LEAF(s) -> Printf.fprintf oc "*(%s)*" s
	| NODE(s,tl) ->
		begin
			Printf.fprintf oc "(%s: [" s;
			List.iter (fun childs -> 
				tree_print oc childs;
				Printf.fprintf oc ";") tl;
			Printf.fprintf oc "])"
		end
		