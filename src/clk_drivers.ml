(*
 * Description : clk_drivers.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

open Exceptions
open Clk_model
open Sig_abs

(** yices type to string *)
let rec yices_types_to_string ytype =
	match ytype with
		Y_NOTYPE -> ""
	|	Y_BOOL -> "bool"
	| Y_NAT -> "nat"
	| Y_INT -> "int"
	| Y_REAL -> "real"
	| Y_FUNC(tyl,ty) -> let res = List.fold_left (fun str ty -> str ^ " " ^ (yices_types_to_string ty)) "" tyl in
		"->" ^ res ^ " " ^ (yices_types_to_string ty) (** name, domain list, and range *)
	| Y_TUPLE(tyl) -> let res = List.fold_left (fun str ty -> str ^ " " ^ (yices_types_to_string ty)) "" tyl in
		"tuple" ^ res
	| Y_RECORD(n,fl) -> let res = List.fold_left (fun str (idf,ty) -> str ^ " " ^ idf ^ "::" ^ (yices_types_to_string ty)) "" fl in
		"record" ^ res (** name, fields list *)
	| Y_SCALAR(n,strl) -> let res = List.fold_left (fun str1 str2 -> str1 ^ " " ^ str2) "" strl in
		"scalar" ^ res (** name, values *)
	| Y_NAMED_TYPED(s) -> if ((compare s "event") == 0) then "bool" else s
	| Y_COMPLEX -> "complex (tuple real real)"
	| Y_ARRAY(yty) -> "array (-> int " ^ (yices_types_to_string yty) ^ ")"
	| Y_CONST(yty) -> yices_types_to_string yty
	
(** -------------------------------------------------------------------- *)

(** yices expr to buffer string *)
let rec yices_expr_to_buff yexpr =
	let bres = Buffer.create 16 in
	match yexpr with
		Y_NOTHING -> bres
	(** variable *)
	| Y_VAR(s) -> begin Buffer.add_string bres s; bres end
	(** constants *) 
	| Y_CTRUE -> begin Buffer.add_string bres "true"; bres end 
	| Y_CFALSE -> begin Buffer.add_string bres "false"; bres end
	| Y_CNAT(s) -> begin Buffer.add_string bres s; bres end
	|	Y_CINT(s) -> begin Buffer.add_string bres s; bres end
	| Y_CREAL(s) -> begin Buffer.add_string bres s; bres end
	| Y_CCOMPLEX(r,i) -> begin Buffer.add_string bres ("(mk-tuple " ^ r ^ " " ^ i ^ ")"); bres end
	| Y_CCHAR(s) -> begin Buffer.add_string bres s; bres end
	| Y_CSTRING(s) -> begin Buffer.add_string bres s; bres end
	| Y_ABSENCE(ty) -> begin Buffer.add_string bres ((yices_types_to_string ty) ^ "_absence"); bres end
	(** boolean *)
	| Y_AND(el) -> 
		begin
			let bres_tmp = Buffer.create 16 in
			List.iter (fun e -> 
								 let btmp = yices_expr_to_buff e in
								 if ((Buffer.length btmp) > 0) then
								 	begin
										Buffer.add_string bres_tmp " ";
										Buffer.add_buffer bres_tmp btmp
								 	end
								 else ()
								 ) el;
			if ((Buffer.length bres_tmp) > 0) then 
				begin
					Buffer.add_string bres "(and";
					Buffer.add_buffer bres bres_tmp;
					Buffer.add_string bres ")";
					Buffer.reset bres_tmp
				end
			else Buffer.reset bres_tmp;
			bres
		end
	| Y_OR(el) ->
		begin
			let bres_tmp = Buffer.create 16 in
			List.iter (fun e -> 
								 let btmp = yices_expr_to_buff e in
								 if ((Buffer.length btmp) > 0) then
								 	begin
										Buffer.add_string bres_tmp " ";
										Buffer.add_buffer bres_tmp btmp
								 	end
								 else ()
								 ) el;
			if ((Buffer.length bres_tmp) > 0) then 
				begin
					Buffer.add_string bres "(or";
					Buffer.add_buffer bres bres_tmp;
					Buffer.add_string bres ")";
					Buffer.reset bres_tmp
				end
			else Buffer.reset bres_tmp;
			bres
		end
	| Y_NOT(e) ->
		begin
			let b_tmp = yices_expr_to_buff e in
			if ((Buffer.length b_tmp) > 0) then
				begin
					Buffer.add_string bres "(not "; 
					Buffer.add_buffer bres b_tmp; 
					Buffer.add_string bres ")"; bres
				end
			else bres
		end
	| Y_IMPLY(e1,e2) ->
		begin
			let b_tmp1 = yices_expr_to_buff e1 and b_tmp2 = yices_expr_to_buff e2 in
			if ((Buffer.length b_tmp1) > 0) then
				begin
					if ((Buffer.length b_tmp2) > 0) then
						begin
							Buffer.add_string bres "(=> "; Buffer.add_buffer bres b_tmp1;
							Buffer.add_string bres " "; Buffer.add_buffer bres b_tmp2; 
							Buffer.add_string bres ")"
						end
					else Buffer.add_buffer bres b_tmp1;
				end 
			else Buffer.add_buffer bres b_tmp2; 
			bres
		end			
	(** equality *)
	| Y_EQ(e1,e2) ->
		begin
			let b_tmp1 = yices_expr_to_buff e1 and b_tmp2 = yices_expr_to_buff e2 in
			if ((Buffer.length b_tmp1) > 0) then
				begin
					if ((Buffer.length b_tmp2) > 0) then
						begin
							Buffer.add_string bres "(= "; Buffer.add_buffer bres b_tmp1;
							Buffer.add_string bres " "; Buffer.add_buffer bres b_tmp2; 
							Buffer.add_string bres ")"
						end
					else Buffer.add_buffer bres b_tmp1;
				end 
			else Buffer.add_buffer bres b_tmp2; 
			bres
		end
	| Y_DIFF(e1,e2) ->
		begin
			let b_tmp1 = yices_expr_to_buff e1 and b_tmp2 = yices_expr_to_buff e2 in
			if ((Buffer.length b_tmp1) > 0) then
				begin
					if ((Buffer.length b_tmp2) > 0) then
						begin
							Buffer.add_string bres "(/= "; Buffer.add_buffer bres b_tmp1;
							Buffer.add_string bres " "; Buffer.add_buffer bres b_tmp2; 
							Buffer.add_string bres ")"
						end
					else
						Buffer.add_buffer bres b_tmp1;
				end 
			else
				Buffer.add_buffer bres b_tmp2;
			bres
		end	
	(** quantifier *)
	| Y_FORALL(idl,e) ->
		begin
			match e with
			| Y_NOTHING -> bres
			| _ ->
				begin
					let res = List.fold_left (fun str (idf,ty) -> str ^ " " ^ idf ^ "::" ^ (yices_types_to_string ty)) "" idl in
					Buffer.add_string bres ("(forall (" ^ res ^ ") "); Buffer.add_buffer bres (yices_expr_to_buff e);
					Buffer.add_string bres ")"; bres
				end
		end
	| Y_EXIST(idl,e) ->
		begin
			match e with
			| Y_NOTHING -> bres
			| _ ->
				begin
					let res = List.fold_left (fun str (idf,ty) -> str ^ " " ^ idf ^ "::" ^ (yices_types_to_string ty)) "" idl in
					Buffer.add_string bres ("(exists (" ^ res ^ ") "); Buffer.add_buffer bres (yices_expr_to_buff e);
					Buffer.add_string bres ")"; bres
				end
		end	
	(** arithmetic *)
	| Y_ADD(e1,e2) ->
		begin
			let b_tmp1 = yices_expr_to_buff e1 and b_tmp2 = yices_expr_to_buff e2 in
			if ((Buffer.length b_tmp1) > 0) then
				begin
					if ((Buffer.length b_tmp2) > 0) then
						begin
							Buffer.add_string bres "(+ "; Buffer.add_buffer bres b_tmp1;
							Buffer.add_string bres " "; Buffer.add_buffer bres b_tmp2; 
							Buffer.add_string bres ")"
						end
					else
						Buffer.add_buffer bres b_tmp1;
				end 
			else
				Buffer.add_buffer bres b_tmp2;
			bres
		end
	| Y_MINUS(e1,e2) ->
		begin
			let b_tmp1 = yices_expr_to_buff e1 and b_tmp2 = yices_expr_to_buff e2 in
			if ((Buffer.length b_tmp1) > 0) then
				begin
					if ((Buffer.length b_tmp2) > 0) then
						begin
							Buffer.add_string bres "(- "; Buffer.add_buffer bres b_tmp1;
							Buffer.add_string bres " "; Buffer.add_buffer bres b_tmp2; 
							Buffer.add_string bres ")"
						end
					else
						Buffer.add_buffer bres b_tmp1;
				end 
			else
				Buffer.add_buffer bres b_tmp2;
			bres
		end
	| Y_MULT(e1,e2) ->
		begin
			let b_tmp1 = yices_expr_to_buff e1 and b_tmp2 = yices_expr_to_buff e2 in
			if ((Buffer.length b_tmp1) > 0) then
				begin
					if ((Buffer.length b_tmp2) > 0) then
						begin
							Buffer.add_string bres "(* "; Buffer.add_buffer bres b_tmp1;
							Buffer.add_string bres " "; Buffer.add_buffer bres b_tmp2; 
							Buffer.add_string bres ")"
						end
					else
						Buffer.add_buffer bres b_tmp1;
				end 
			else
				Buffer.add_buffer bres b_tmp2;
			bres
		end
	| Y_DIV(e1,e2) ->
		begin
			let b_tmp1 = yices_expr_to_buff e1 and b_tmp2 = yices_expr_to_buff e2 in
			if ((Buffer.length b_tmp1) > 0) then
				begin
					if ((Buffer.length b_tmp2) > 0) then
						begin
							Buffer.add_string bres "(/ "; Buffer.add_buffer bres b_tmp1;
							Buffer.add_string bres " "; Buffer.add_buffer bres b_tmp2; 
							Buffer.add_string bres ")"
						end
					else
						Buffer.add_buffer bres b_tmp1;
				end 
			else
				Buffer.add_buffer bres b_tmp2;
			bres
		end
	| Y_INTDIV(e1,e2) ->
		begin
			let b_tmp1 = yices_expr_to_buff e1 and b_tmp2 = yices_expr_to_buff e2 in
			if ((Buffer.length b_tmp1) > 0) then
				begin
					if ((Buffer.length b_tmp2) > 0) then
						begin
							Buffer.add_string bres "(div "; Buffer.add_buffer bres b_tmp1;
							Buffer.add_string bres " "; Buffer.add_buffer bres b_tmp2; 
							Buffer.add_string bres ")"
						end
					else
						Buffer.add_buffer bres b_tmp1;
				end 
			else
				Buffer.add_buffer bres b_tmp2;
			bres
		end
	| Y_MOD(e1,e2) ->
		begin
			let b_tmp1 = yices_expr_to_buff e1 and b_tmp2 = yices_expr_to_buff e2 in
			if ((Buffer.length b_tmp1) > 0) then
				begin
					if ((Buffer.length b_tmp2) > 0) then
						begin
							Buffer.add_string bres "(mod "; Buffer.add_buffer bres b_tmp1;
							Buffer.add_string bres " "; Buffer.add_buffer bres b_tmp2; 
							Buffer.add_string bres ")"
						end
					else
						Buffer.add_buffer bres b_tmp1;
				end 
			else
				Buffer.add_buffer bres b_tmp2;
			bres
		end
	| Y_LT(e1,e2) ->
		begin
			let b_tmp1 = yices_expr_to_buff e1 and b_tmp2 = yices_expr_to_buff e2 in
			if ((Buffer.length b_tmp1) > 0) then
				begin
					if ((Buffer.length b_tmp2) > 0) then
						begin
							Buffer.add_string bres "(< "; Buffer.add_buffer bres b_tmp1;
							Buffer.add_string bres " "; Buffer.add_buffer bres b_tmp2; 
							Buffer.add_string bres ")"
						end
					else
						Buffer.add_buffer bres b_tmp1;
				end 
			else
				Buffer.add_buffer bres b_tmp2;
			bres
		end
	| Y_LTE(e1,e2) ->
		begin
			let b_tmp1 = yices_expr_to_buff e1 and b_tmp2 = yices_expr_to_buff e2 in
			if ((Buffer.length b_tmp1) > 0) then
				begin
					if ((Buffer.length b_tmp2) > 0) then
						begin
							Buffer.add_string bres "(<= "; Buffer.add_buffer bres b_tmp1;
							Buffer.add_string bres " "; Buffer.add_buffer bres b_tmp2; 
							Buffer.add_string bres ")"
						end
					else
						Buffer.add_buffer bres b_tmp1;
				end 
			else
				Buffer.add_buffer bres b_tmp2;
			bres
		end
	| Y_GT(e1,e2) ->
		begin
			let b_tmp1 = yices_expr_to_buff e1 and b_tmp2 = yices_expr_to_buff e2 in
			if ((Buffer.length b_tmp1) > 0) then
				begin
					if ((Buffer.length b_tmp2) > 0) then
						begin
							Buffer.add_string bres "(> "; Buffer.add_buffer bres b_tmp1;
							Buffer.add_string bres " "; Buffer.add_buffer bres b_tmp2; 
							Buffer.add_string bres ")"
						end
					else
						Buffer.add_buffer bres b_tmp1;
				end 
			else
				Buffer.add_buffer bres b_tmp2;
			bres
		end
	| Y_GTE(e1,e2) ->
		begin
			let b_tmp1 = yices_expr_to_buff e1 and b_tmp2 = yices_expr_to_buff e2 in
			if ((Buffer.length b_tmp1) > 0) then
				begin
					if ((Buffer.length b_tmp2) > 0) then
						begin
							Buffer.add_string bres "(>= "; Buffer.add_buffer bres b_tmp1;
							Buffer.add_string bres " "; Buffer.add_buffer bres b_tmp2; 
							Buffer.add_string bres ")"
						end
					else
						Buffer.add_buffer bres b_tmp1;
				end 
			else
				Buffer.add_buffer bres b_tmp2;
			bres
		end	
	(** others *)
	| Y_FUNCALL(name,el) ->
		begin
			Buffer.add_string bres ("(" ^ name);
			List.iter (fun e -> 
				match e with
				| Y_NOTHING -> ()
				| _ -> 
					begin
						Buffer.add_string bres " ";
						Buffer.add_buffer bres (yices_expr_to_buff e)
					end) el;
			Buffer.add_string bres ")"; bres
		end
	| Y_MKTUPLE(el) ->
		begin
			Buffer.add_string bres "(mk-tuple";
			List.iter (fun e -> 
				match e with 
				| Y_NOTHING -> ()
				| _ ->
					begin
						Buffer.add_string bres " "; 
						Buffer.add_buffer bres (yices_expr_to_buff e)
					end) el;
			Buffer.add_string bres ")"; bres
		end
	| Y_SELECT_TUPLE(e1,e2) ->
		begin
		match (e1,e2) with
		| ((Y_NOTHING,_) | (_,Y_NOTHING)) -> bres
		| (_,_) ->
			begin
				Buffer.add_string bres "(select ";
				Buffer.add_buffer bres (yices_expr_to_buff e1);
				Buffer.add_string bres " ";
				Buffer.add_buffer bres (yices_expr_to_buff e2);
				Buffer.add_string bres ")"; bres
			end
		end
	| Y_UPDATE_TUPLE(e1,e2,e3) ->
		begin
			match (e1,e2,e3) with
			| ((Y_NOTHING,_,_) | (_,Y_NOTHING,_) | (_,_,Y_NOTHING)) -> bres
			| (_,_,_) ->
				begin
					Buffer.add_string bres "(update ";
					Buffer.add_buffer bres (yices_expr_to_buff e1);
					Buffer.add_string bres " ";
					Buffer.add_buffer bres (yices_expr_to_buff e2);
					Buffer.add_string bres " ";
					Buffer.add_buffer bres (yices_expr_to_buff e3);
					Buffer.add_string bres ")"; bres
				end
		end
	| Y_MKRECORD(fl) ->
		begin
			Buffer.add_string bres "(mk-record";
			List.iter (fun (id,e) -> 
				match e with
				| Y_NOTHING -> ()
				| _ ->
					begin
						Buffer.add_string bres (" " ^ id); 
						Buffer.add_buffer bres (yices_expr_to_buff e)
					end) fl;
			Buffer.add_string bres ")"; bres
		end
	| Y_SELECT_RECORD(e1,e2) ->
		begin
		match (e1,e2) with
		| ((Y_NOTHING,_) | (_,Y_NOTHING)) -> bres
		| (_,_) ->
			begin
				Buffer.add_string bres "(select ";
				Buffer.add_buffer bres (yices_expr_to_buff e1);
				Buffer.add_string bres " ";
				Buffer.add_buffer bres (yices_expr_to_buff e2);
				Buffer.add_string bres ")"; bres
			end
		end
	| Y_UPDATE_RECORD(e1,e2,e3) ->
		begin
		match (e1,e2,e3) with
		| ((Y_NOTHING,_,_) | (_,Y_NOTHING,_) | (_,_,Y_NOTHING)) -> bres
		| (_,_,_) ->
			begin
				Buffer.add_string bres "(update ";
				Buffer.add_buffer bres (yices_expr_to_buff e1);
				Buffer.add_string bres " ";
				Buffer.add_buffer bres (yices_expr_to_buff e2);
				Buffer.add_string bres " ";
				Buffer.add_buffer bres (yices_expr_to_buff e3);
				Buffer.add_string bres ")"; bres
			end
		end
		
(** --------------------------------------------------------------------- *)

let and_yices_exprl_list yexprl =
	if ((List.length yexprl) = 0) then Y_NOTHING
	else if ((List.length yexprl) == 1) then List.hd yexprl
	else Y_AND(yexprl)
	
(** --------------------------------------------------------------------- *)

(** translate a declaration to buffer *)
let yices_declaration_to_buff ydec =
	match ydec with
		Y_TYPEDEF(ty,name) ->
		begin
			let bres = Buffer.create 16 in
			match ty with
			| Y_NOTYPE -> Buffer.add_string bres ("(define-type " ^ name ^ ")"); bres
			| _ -> Buffer.add_string bres ("(define-type " ^ name ^ " " ^ (yices_types_to_string ty) ^ ")"); bres
		end
	| Y_VARDEF(ty,(name,expr)) ->
		begin
			let bres = Buffer.create 16 in
			match expr with
			| Y_NOTHING -> Buffer.add_string bres ("(define " ^ name ^ "::" ^ (yices_types_to_string ty) ^ ")"); bres
			| _ -> Buffer.add_string bres ("(define " ^ name ^ "::" ^ (yices_types_to_string ty) ^ " "); 
						 Buffer.add_buffer bres (yices_expr_to_buff expr); bres
		end		

(** --------------------------------------------------------------------- *)		

(** is event type *)
let is_event_type yty =
	match yty with
	| Y_NAMED_TYPED(byty) ->
		if ((compare byty "event") == 0) then true
		else false
	| Y_CONST(ybty) ->
		begin
			match ybty with
			| Y_NAMED_TYPED(byty) ->
				if ((compare byty "event") == 0) then true
				else false
			| _ -> false
		end
	| _ -> false

(** --------------------------------------------------------------------- *)

(** sig_types to yices_types *)
let rec sig_abs_to_yices_abs_types sig_type typedefs =
	match sig_type with
		NO_TYPE -> Y_NOTYPE
	|	T_EVENT -> Y_NAMED_TYPED("event")
	| T_BOOL -> Y_BOOL
	| T_INT(sz,sg) -> 
		begin
			match sg with
			| UNSIGNED -> Y_NAT
			| _ -> Y_INT
		end
	| T_REAL -> Y_REAL
	| T_COMPLEX -> Y_COMPLEX
	| T_CHAR(sg) -> Y_NAMED_TYPED("char")
	| T_STRING -> Y_NAMED_TYPED("string")
	| T_ENUM(n,nl) -> Y_SCALAR(n,nl)
	| T_ARRAY(ty,sz) -> 
		begin
			let domain = ref [] in
			for i = 1 to (List.length sz) do domain := !domain @ [Y_INT] done;
			Y_ARRAY(Y_FUNC(!domain,(sig_abs_to_yices_abs_types ty typedefs)))
		end
	| T_STRUCT(n,fil) -> 
		begin
			let ufil = List.map (fun (varc,base_ty,(name,initexpr)) -> (name,(sig_abs_to_yices_abs_types base_ty typedefs))) fil in
			Y_RECORD(n,ufil)
		end
	| T_BUNDLE(n,fil,initexpr) ->
		begin
			let ufil = List.map (fun (varc,base_ty,(name,initexpr)) -> (name,(sig_abs_to_yices_abs_types base_ty typedefs))) fil in
			Y_RECORD(n,ufil)
		end
	| T_EXTERNAL(s) -> Y_NAMED_TYPED(s)
	| T_CONST(ty) -> sig_abs_to_yices_abs_types ty typedefs
	| T_NAMED_TYPED(s) -> 
		begin
			try
				let basetype = get_basetype_typedef typedefs sig_type in
				match basetype with
				| NO_TYPE -> Y_NAMED_TYPED(s)
				| _ -> sig_abs_to_yices_abs_types basetype typedefs
			with TypedefNotFound(typemsg) -> Y_NAMED_TYPED(s)
		end
	| T_PROCESS(n) -> Y_NOTYPE
	| T_TUPLES(tyl) ->
		begin
			let ytyl = List.map (fun ty -> sig_abs_to_yices_abs_types ty typedefs) tyl in
			Y_TUPLE(ytyl)
		end

(** --------------------------------------------------------------------- *)

(** create fresh name *)
let create_fresh_vars expr = 
	let snews = "locvar" ^ (string_of_int (Id_counter.next_newvar_id ())) in 
	(* note implemented now: add to the hash *)
	(* Hashtbls.add_freshvar_hashtbl expr snews; *)
	(("h_" ^ snews),("v_" ^ snews))

(** --------------------------------------------------------------------- *)	

(** create fresh memorized var name *)
let create_memorized_vars str =
	let (pre,init) = (("pre_" ^ str),("init_" ^ str)) in
	(* add to the hash *)
	Hashtbls.add_prevar_hashtbl pre str;
	(pre,init)

(** --------------------------------------------------------------------- *)

(** create constant symbol *)
let create_const_vars expr = 
	let snews = "cst_" ^ (string_of_int (Id_counter.next_newconstant_id ())) in
	(* add to the hashs *)
	Hashtbls.add_const_hashtbl expr snews;
	Hashtbls.add_val_const_hashtbl snews expr;
	snews
	
(** --------------------------------------------------------------------- *)

(** create fresh memorized var name *)
let create_uninterpreted_vars expr op ord1 ord2 =
	let snews = "unint_" ^ op ^ "_" ^ (string_of_int (Id_counter.next_newunint_id ())) in
	(* add it to hash *)
	Hashtbls.add_unint_hashtbl expr snews;
	Hashtbls.add_val_unint_hashtbl snews (op,ord1,ord2);
	(("h_" ^ snews),("v_" ^ snews))
	
(** --------------------------------------------------------------------- *)

(** S_CLKHAT to yices *)
let clkhat_expr_to_ycies expr c v vt cc vc nv mode lhsclk lhsvalue =
	match vt with
	| Y_CONST(y_bty) -> raise (InvalidExprssion (expr_to_string expr))
	| _ ->
		if (mode == 0) then
			(* create a fresh symbol *)
			let (newclk,newval) = create_fresh_vars expr in
			(Y_VAR(newclk),
			Y_VAR(newval),
			Y_NAMED_TYPED("event"),
			[Y_EQ(Y_VAR(newclk),c)]@cc,
			[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc,
			[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv)
		else
			(lhsclk,
			lhsvalue,
			Y_NAMED_TYPED("event"),
			[Y_EQ(lhsclk,c)]@cc,
			[Y_IMPLY(lhsclk,lhsvalue);
       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc,
			nv)
				
(** --------------------------------------------------------------------- *)

(** S_CLKWHEN to yices *)
let clkwhen_expr_to_ycies expr c v vt cc vc nv mode lhsclk lhsvalue =
  if (mode == 0) then
		begin
  		match vt with
    	| Y_CONST(y_bty) ->
    		begin
    			match v with
    			| Y_CTRUE -> (Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc,vc,nv)
    			| Y_CFALSE -> (Y_CFALSE,Y_NOTHING,Y_NOTYPE,cc,vc,nv)
    			| _ -> raise (InvalidExprssion (expr_to_string expr))
    		end
    	| _ ->
  			let (newclk,newval) = create_fresh_vars expr in
  			(Y_VAR(newclk),
  			Y_VAR(newval),
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(Y_VAR(newclk),Y_AND([c;v]))]@cc,
  			[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
         Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc,
  			[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv)
		end
	else
		begin
			match vt with
    	| Y_CONST(y_bty) ->
    		begin
    			match v with
    			| Y_CTRUE -> 
						(lhsclk,
      			lhsvalue,
      			Y_NAMED_TYPED("event"),
      			cc,
      			[Y_IMPLY(lhsclk,lhsvalue);
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc,
      			nv)
    			| Y_CFALSE -> 
						(lhsclk,
      			lhsvalue,
      			Y_NOTYPE,
      			[Y_EQ(lhsclk,Y_CFALSE)]@cc,
      			vc,
      			nv)
    			| _ -> raise (InvalidExprssion (expr_to_string expr))
    		end
    	| _ ->
				(lhsclk,
  			lhsvalue,
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(lhsclk,Y_AND([c;v]))]@cc,
  			[Y_IMPLY(lhsclk,lhsvalue);
         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc,
  			nv)
		end
				
(** --------------------------------------------------------------------- *)

(** S_CLKPLUS to yices *)
let clkplus_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
    	match (vt1,vt2) with
    	| (Y_CONST(_),Y_CONST(_)) -> raise (InvalidExprssion (expr_to_string expr))
			| (Y_CONST(_),_) ->
				let (newclk,newval) = create_fresh_vars expr in 
  			(Y_VAR(newclk),
  			Y_VAR(newval),
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(Y_VAR(newclk),Y_OR([Y_VAR(newclk);c2]))]@cc1@cc2,
  			[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
         Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  			[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
			| (_,Y_CONST(_)) ->
				let (newclk,newval) = create_fresh_vars expr in 
  			(Y_VAR(newclk),
  			Y_VAR(newval),
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(Y_VAR(newclk),Y_OR([c1;Y_VAR(newclk)]))]@cc1@cc2,
  			[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
         Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  			[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    	| _ ->
  			let (newclk,newval) = create_fresh_vars expr in 
  			(Y_VAR(newclk),
  			Y_VAR(newval),
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(Y_VAR(newclk),Y_OR([c1;c2]))]@cc1@cc2,
  			[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
         Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  			[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
		end
	else
		begin
			match (vt1,vt2) with
    	| (Y_CONST(_),Y_CONST(_)) -> raise (InvalidExprssion (expr_to_string expr))
			| (Y_CONST(_),_) ->
  			(lhsclk,
  			lhsvalue,
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(lhsclk,Y_OR([lhsclk;c2]))]@cc1@cc2,
  			[Y_IMPLY(lhsclk,lhsvalue);
         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  			nv1@nv2)
			| (_,Y_CONST(_)) ->
  			(lhsclk,
  			lhsvalue,
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(lhsclk,Y_OR([c1;lhsclk]))]@cc1@cc2,
  			[Y_IMPLY(lhsclk,lhsvalue);
         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  			nv1@nv2)
    	| _ ->
  			(lhsclk,
  			lhsvalue,
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(lhsclk,Y_OR([c1;c2]))]@cc1@cc2,
  			[Y_IMPLY(lhsclk,lhsvalue);
         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
  			nv1@nv2)
		end
				
(** --------------------------------------------------------------------- *)

(** S_CLKMINUS to yices *)
let clkminus_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
  		match (vt1,vt2) with
  		| (Y_CONST(_),Y_CONST(_)) -> raise (InvalidExprssion (expr_to_string expr))
  		| (Y_CONST(_),_) ->
				let (newclk,newval) = create_fresh_vars expr in 
				(Y_VAR(newclk),
				Y_VAR(newval),
				Y_NAMED_TYPED("event"),
				[Y_EQ(Y_VAR(newclk),Y_AND([Y_VAR(newclk);Y_NOT(c2)]))]@cc1@cc2,
				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
				[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
			| (_,Y_CONST(_)) ->
				let (newclk,newval) = create_fresh_vars expr in 
				(Y_VAR(newclk),
				Y_VAR(newval),
				Y_NAMED_TYPED("event"),
				[Y_EQ(Y_VAR(newclk),Y_AND([c1;Y_NOT(Y_VAR(newclk))]))]@cc1@cc2,
				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
				[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
			| _ ->
				let (newclk,newval) = create_fresh_vars expr in 
				(Y_VAR(newclk),
				Y_VAR(newval),
				Y_NAMED_TYPED("event"),
				[Y_EQ(Y_VAR(newclk),Y_AND([c1;Y_NOT(c2)]))]@cc1@cc2,
				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
				[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
		end
	else
		begin
			match (vt1,vt2) with
  		| (Y_CONST(_),Y_CONST(_)) -> raise (InvalidExprssion (expr_to_string expr))
			| (Y_CONST(_),_) ->
				(lhsclk,
				lhsvalue,
				Y_NAMED_TYPED("event"),
				[Y_EQ(lhsclk,Y_AND([lhsclk;Y_NOT(c2)]))]@cc1@cc2,
				[Y_IMPLY(lhsclk,lhsvalue);
	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
				nv1@nv2)
			| (_,Y_CONST(_)) ->
				(lhsclk,
				lhsvalue,
				Y_NAMED_TYPED("event"),
				[Y_EQ(lhsclk,Y_AND([c1;Y_NOT(lhsclk)]))]@cc1@cc2,
				[Y_IMPLY(lhsclk,lhsvalue);
	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
				nv1@nv2)
  		| _ ->
				(lhsclk,
				lhsvalue,
				Y_NAMED_TYPED("event"),
				[Y_EQ(lhsclk,Y_AND([c1;Y_NOT(c2)]))]@cc1@cc2,
				[Y_IMPLY(lhsclk,lhsvalue);
	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				nv1@nv2)
		end
		
(** --------------------------------------------------------------------- *)

(** S_CLKMULT to yices *)
let clkmult_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
			match (vt1,vt2) with
    	| (Y_CONST(_),Y_CONST(_)) -> raise (InvalidExprssion (expr_to_string expr))
			| (Y_CONST(_),_) ->
				let (newclk,newval) = create_fresh_vars expr in 
  			(Y_VAR(newclk),
  			Y_VAR(newval),
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(Y_VAR(newclk),Y_AND([Y_VAR(newclk);c2]))]@cc1@cc2,
  			[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
         Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  			[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
			| (_,Y_CONST(_)) ->
				let (newclk,newval) = create_fresh_vars expr in 
  			(Y_VAR(newclk),
  			Y_VAR(newval),
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(Y_VAR(newclk),Y_AND([c1;Y_VAR(newclk)]))]@cc1@cc2,
  			[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
         Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  			[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    	| _ ->
  			let (newclk,newval) = create_fresh_vars expr in 
  			(Y_VAR(newclk),
  			Y_VAR(newval),
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(Y_VAR(newclk),Y_AND([c1;c2]))]@cc1@cc2,
  			[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
         Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  			[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
		end
	else
		begin
			match (vt1,vt2) with
    	| (Y_CONST(_),Y_CONST(_)) -> raise (InvalidExprssion (expr_to_string expr))
			| (Y_CONST(_),_) ->
  			(lhsclk,
  			lhsvalue,
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(lhsclk,Y_AND([lhsclk;c2]))]@cc1@cc2,
  			[Y_IMPLY(lhsclk,lhsvalue);
         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  			nv1@nv2)
			| (_,Y_CONST(_)) ->
  			(lhsclk,
  			lhsvalue,
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(lhsclk,Y_AND([c1;lhsclk]))]@cc1@cc2,
  			[Y_IMPLY(lhsclk,lhsvalue);
         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  			nv1@nv2)
    	| _ ->
  			(lhsclk,
  			lhsvalue,
  			Y_NAMED_TYPED("event"),
  			[Y_EQ(lhsclk,Y_AND([c1;c2]))]@cc1@cc2,
  			[Y_IMPLY(lhsclk,lhsvalue);
         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
  			nv1@nv2)
		end
	
(** --------------------------------------------------------------------- *)

(** S_CONSTANT to yices *)
let constant_expr_to_ycies expr c mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
			match c with
    	| S_TRUE -> (Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),[],[],[])
    	| S_FALSE -> (Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),[],[],[])
    	|	S_INT(ci) -> 
    		begin
    			(* check the symbol is added *)
    			try 
    				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(ci)) in
    				(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),[],[],[])
    			with SymNotFound(smsg) ->
    				(* create a new constant symbol *)	
    				let const_var = create_const_vars (Y_CINT(ci)) in
    				(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),[],[],[(const_var,Y_CONST(Y_INT))])
    		end
    	| S_REAL(cr) -> 
    		begin
    			(* check the symbol is added *)
    			try 
    				let const_var = Hashtbls.get_const_hashtbl (Y_CREAL(cr)) in
    				(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),[],[],[])
    			with SymNotFound(smsg) ->
    				(* create a new constant symbol *)
    				let const_var = create_const_vars (Y_CREAL(cr)) in
    				(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),[],[],[(const_var,Y_CONST(Y_REAL))])
    		end
    	| S_COMPLEX(creal,cimage) -> 
    		begin
    			(* check the symbol is added *)
    			try 
    				let const_var = Hashtbls.get_const_hashtbl (Y_CCOMPLEX(creal,cimage)) in
    				(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),[],[],[])
    			with SymNotFound(smsg) ->
    				(* create a new constant symbol *)	
    				let const_var = create_const_vars (Y_CCOMPLEX(creal,cimage)) in
    				(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),[],[],[(const_var,Y_CONST(Y_COMPLEX))])
    		end
    	| S_CHAR(cchar) -> 
    		begin
    			(* check the symbol is added *)
    			try 
    				let const_var = Hashtbls.get_const_hashtbl (Y_CCHAR(cchar)) in
    				(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_NAMED_TYPED("char")),[],[],[])
    			with SymNotFound(smsg) ->
    				(* create a new constant symbol *)	
    				let const_var = create_const_vars (Y_CCHAR(cchar)) in
    				(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_NAMED_TYPED("char")),[],[],[(const_var,Y_NAMED_TYPED("char"))])
    		end
    	| S_STRING(cstr) -> 
    		begin
    			(* check the symbol is added *)
    			try 
    				let const_var = Hashtbls.get_const_hashtbl (Y_CSTRING(cstr)) in
    				(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_NAMED_TYPED("string")),[],[],[])
    			with SymNotFound(smsg) ->
    				(* create a new constant symbol *)
    				let const_var = create_const_vars (Y_CSTRING(cstr)) in
    				(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_NAMED_TYPED("string")),[],[],[(const_var,Y_CONST(Y_NAMED_TYPED("string")))])
    		end
		end
	else
		begin
			match c with
    	| S_TRUE -> 
				(lhsclk,
  			lhsvalue,
  			Y_NAMED_TYPED("event"),
  			[],
  			[Y_IMPLY(lhsclk,lhsvalue);
         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))],
  			[])
    	| S_FALSE -> 
				(lhsclk,
  			lhsvalue,
  			Y_BOOL,
  			[],
  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))],
  			[])
    	|	S_INT(ci) -> 
    		begin
    			(* check the symbol is added *)
    			try 
    				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(ci)) in
						(lhsclk,
      			lhsvalue,
      			Y_INT,
      			[],
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))],
      			[])
    			with SymNotFound(smsg) ->
    			(* create a new constant symbol *)	
    				let const_var = create_const_vars (Y_CINT(ci)) in
						(lhsclk,
      			lhsvalue,
      			Y_INT,
      			[],
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))],
      			[(const_var,Y_CONST(Y_INT))])
    		end
    	| S_REAL(cr) -> 
    		begin
    			(* check the symbol is added *)
    			try 
    				let const_var = Hashtbls.get_const_hashtbl (Y_CREAL(cr)) in
						(lhsclk,
      			lhsvalue,
      			Y_REAL,
      			[],
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))],
      			[])
    			with SymNotFound(smsg) ->
    			(* create a new constant symbol *)
    				let const_var = create_const_vars (Y_CREAL(cr)) in
						(lhsclk,
      			lhsvalue,
      			Y_REAL,
      			[],
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))],
      			[(const_var,Y_CONST(Y_REAL))])
    		end
    	| S_COMPLEX(creal,cimage) -> 
    		begin
    			(* check the symbol is added *)
    			try 
    				let const_var = Hashtbls.get_const_hashtbl (Y_CCOMPLEX(creal,cimage)) in
						(lhsclk,
      			lhsvalue,
      			Y_COMPLEX,
      			[],
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))],
      			[])
    			with SymNotFound(smsg) ->
    				(* create a new constant symbol *)	
    				let const_var = create_const_vars (Y_CCOMPLEX(creal,cimage)) in
						(lhsclk,
      			lhsvalue,
      			Y_COMPLEX,
      			[],
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))],
      			[(const_var,Y_CONST(Y_COMPLEX))])
    		end
    	| S_CHAR(cchar) -> 
    		begin
    			(* check the symbol is added *)
    			try 
    				let const_var = Hashtbls.get_const_hashtbl (Y_CCHAR(cchar)) in
						(lhsclk,
      			lhsvalue,
      			Y_NAMED_TYPED("char"),
      			[],
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("char"))))],
      			[])
    			with SymNotFound(smsg) ->
    				(* create a new constant symbol *)	
    				let const_var = create_const_vars (Y_CCHAR(cchar)) in
						(lhsclk,
      			lhsvalue,
      			Y_NAMED_TYPED("char"),
      			[],
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("char"))))],
      			[(const_var,Y_CONST(Y_NAMED_TYPED("char")))])
    		end
    	| S_STRING(cstr) -> 
    		begin
    			(* check the symbol is added *)
    			try 
    				let const_var = Hashtbls.get_const_hashtbl (Y_CSTRING(cstr)) in
						(lhsclk,
      			lhsvalue,
      			Y_NAMED_TYPED("string"),
      			[],
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("string"))))],
      			[])
    			with SymNotFound(smsg) ->
    				(* create a new constant symbol *)
    				let const_var = create_const_vars (Y_CSTRING(cstr)) in
						(lhsclk,
      			lhsvalue,
      			Y_NAMED_TYPED("string"),
      			[],
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("string"))))],
      			[(const_var,Y_CONST(Y_NAMED_TYPED("string")))])
    		end
		end

(** --------------------------------------------------------------------- *)

(** S_ENUMITEM to yices *)
let enumitem_expr_to_ycies s e typedefs c v vt cc vc nv mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
    	match e with
      	| S_CONSTANT(S_STRING(elemname)) ->
      		begin
      			if ((compare s "") == 0) then
      				begin
      					let (res,ty,name) = find_enumdef_in_decs typedefs elemname in
      					match ty with
      					| T_ENUM(enumname,enumvalues) ->
      						(Y_NOTHING,v,Y_CONST(Y_SCALAR(enumname,enumvalues)),cc,vc,nv)
      					| _ -> raise (InvalidExprssion (expr_to_string (S_ENUMITEM(s,e))))
      				end
      			else
      				begin
      					let (res,ty,name) = find_typedef_in_decs typedefs s in
      					match ty with
      					| T_ENUM(enumname,enumvalues) ->
      						(Y_NOTHING,v,Y_CONST(Y_SCALAR(enumname,enumvalues)),cc,vc,nv)
      					| _ -> raise (InvalidExprssion (expr_to_string (S_ENUMITEM(s,e))))
      				end
      		end
      	| _ -> raise (InvalidExprssion (expr_to_string (S_ENUMITEM(s,e))))
		end
	else
		begin
			match e with
      	| S_CONSTANT(S_STRING(elemname)) ->
      		begin
      			if ((compare s "") == 0) then
      				begin
      					let (res,ty,name) = find_enumdef_in_decs typedefs elemname in
      					match ty with
      					| T_ENUM(enumname,enumvalues) ->
									(lhsclk,
									lhsvalue,
									Y_SCALAR(enumname,enumvalues),
									cc,
									[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v));
             			 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_SCALAR(enumname,enumvalues))))]@vc,
									nv)
      					| _ -> raise (InvalidExprssion (expr_to_string (S_ENUMITEM(s,e))))
      				end
      			else
      				begin
      					let (res,ty,name) = find_typedef_in_decs typedefs s in
      					match ty with
      					| T_ENUM(enumname,enumvalues) ->
									(lhsclk,
									lhsvalue,
									Y_SCALAR(enumname,enumvalues),
									cc,
									[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v));
             			 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_SCALAR(enumname,enumvalues))))]@vc,
									nv)
      					| _ -> raise (InvalidExprssion (expr_to_string (S_ENUMITEM(s,e))))
      				end
      		end
      	| _ -> raise (InvalidExprssion (expr_to_string (S_ENUMITEM(s,e))))
		end
	
(** --------------------------------------------------------------------- *)

(** S_CAST to yices *)
let cast_expr_to_ycies expr c v vt cc vc nv ty typedefs mode lhsclk lhsvalue =
	match ty with
	| T_EVENT ->
		(c,v,(sig_abs_to_yices_abs_types ty typedefs),cc,[Y_IMPLY(c,v)]@vc,nv)
	| T_NAMED_TYPED(namedtype) ->
		begin
			try
				let basetype = get_basetype_typedef typedefs ty in
				match basetype with
				| T_EVENT -> 
					(c,v,(sig_abs_to_yices_abs_types ty typedefs),cc,[Y_IMPLY(c,v)]@vc,nv)
				| _ -> 
					(c,v,(sig_abs_to_yices_abs_types ty typedefs),cc,vc,nv)
			with TypedefNotFound(msg) -> (c,v,(sig_abs_to_yices_abs_types ty typedefs),cc,vc,nv)
		end
	| _ ->
		(c,v,(sig_abs_to_yices_abs_types ty typedefs),cc,vc,nv)
	
(** --------------------------------------------------------------------- *)
	
(** S_DELAY to yices *)
let delay_expr_to_ycies expr c v vt cc vc nv mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
    	if (is_event_type vt) then
  			let (newclk,newval) = create_fresh_vars expr in
  			(Y_VAR(newclk),
  	 		Y_VAR(newval),
  			vt,
  	 		[Y_EQ(Y_VAR(newclk),c)]@cc,
  	 		[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
  			 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt)))]@vc,
  	 		[(newclk,Y_BOOL);(newval,vt)]@nv)
    	else
    		begin
    			match v with
    			| Y_VAR(varid) ->
  					let (newclk,newval) = create_fresh_vars expr and
  					(memv,_) = create_memorized_vars varid in
  					(Y_VAR(newclk),
  	 				Y_VAR(newval),
  					vt,
  	 				[Y_EQ(Y_VAR(newclk),c)]@cc,
  	 				[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_VAR(memv)));
  			     Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt)))]@vc,
  	 				[(newclk,Y_BOOL);(newval,vt);(memv,vt)]@nv)
    			| _ -> raise (InvalidExprssion (expr_to_string expr))
    		end
		end
	else
		begin
			if (is_event_type vt) then
  			(lhsclk,
  	 		lhsvalue,
  			vt,
  	 		[Y_EQ(lhsclk,c)]@cc,
  	 		[Y_IMPLY(lhsclk,lhsvalue);
  			 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt)))]@vc,
  	 		nv)
    	else
    		begin
    			match v with
    			| Y_VAR(varid) ->
  					let (memv,_) = create_memorized_vars varid in
  					(lhsclk,
  	 				lhsvalue,
  					vt,
  	 				[Y_EQ(lhsclk,c)]@cc,
  	 				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(memv)));
  			     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt)))]@vc,
  	 				[(memv,vt)]@nv)
    			| _ -> raise (InvalidExprssion (expr_to_string expr))
    		end
		end
		
(** --------------------------------------------------------------------- *)
	
(** S_DELAYINIT to yices *)
let delayinit_expr_to_ycies expr c v vt cc vc nv ci vi vti cci vci nvi mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
    	if (is_event_type vt) then
  			let (newclk,newval) = create_fresh_vars expr in
  			(Y_VAR(newclk),
  	 		Y_VAR(newval),
  			vt,
  	 		[Y_EQ(Y_VAR(newclk),c)]@cc,
  	 		[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
  			 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt)))]@vc,
  	 		[(newclk,Y_BOOL);(newval,vt)]@nv)
    	else
    		begin
    			match v with
    			| Y_VAR(varid) ->
  					let (newclk,newval) = create_fresh_vars expr and
  					(memv,memv0) = create_memorized_vars varid in
  					(Y_VAR(newclk),
  	 				Y_VAR(newval),
  					vt,
  	 				[Y_EQ(Y_VAR(newclk),c)]@cc@cci,
  	 				[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_VAR(memv)));
  			     Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt)));
  			 						Y_EQ(Y_VAR(memv0),vi)]@vc@vci,
  	 				[(newclk,Y_BOOL);(newval,vt);(memv,vt);(memv0,vt)]@nv@nvi)
    			|_ -> raise (InvalidExprssion (expr_to_string expr))
    		end
			end
		else
			begin
				if (is_event_type vt) then
  			(lhsclk,
  	 		lhsvalue,
  			vt,
  	 		[Y_EQ(lhsclk,c)]@cc,
  	 		[Y_IMPLY(lhsclk,lhsvalue);
  			 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt)))]@vc,
  	 		nv)
    	else
    		begin
    			match v with
    			| Y_VAR(varid) ->
  					let (memv,memv0) = create_memorized_vars varid in
  					(lhsclk,
  	 				lhsvalue,
  					vt,
  	 				[Y_EQ(lhsclk,c)]@cc@cci,
  	 				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(memv)));
  			     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt)));
  			 						Y_EQ(Y_VAR(memv0),vi)]@vc@vci,
  	 				[(memv,vt);(memv0,vt)]@nv@nvi)
    			|_ -> raise (InvalidExprssion (expr_to_string expr))
    		end
			end
		
(** --------------------------------------------------------------------- *)

(** S_DELAYBY to yices *)
let delayby_expr_to_ycies expr c v vt cc vc nv mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
    	if (is_event_type vt) then
  			let (newclk,newval) = create_fresh_vars expr in
  			(Y_VAR(newclk),
  	 		Y_VAR(newval),
  			vt,
  	 		[Y_EQ(Y_VAR(newclk),c)]@cc,
  	 		[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
  			 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt)))]@vc,
  	 		[(newclk,Y_BOOL);(newval,vt)]@nv)
    	else
    		begin
    			match v with
    			| Y_VAR(varid) ->
  					let (newclk,newval) = create_fresh_vars expr and
  					(memv,_) = create_memorized_vars varid in
  					(Y_VAR(newclk),
  	 				Y_VAR(newval),
  					vt,
  	 				[Y_EQ(Y_VAR(newclk),c)]@cc,
  	 				[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_VAR(memv)));
  			     Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt)))]@vc,
  	 				[(newclk,Y_BOOL);(newval,vt);(memv,vt)]@nv)
    			| _ -> raise (InvalidExprssion (expr_to_string expr))
    		end
			end
		else
			begin
				if (is_event_type vt) then
  				(lhsclk,
  	 			lhsvalue,
  				vt,
  	 			[Y_EQ(lhsclk,c)]@cc,
  	 			[Y_IMPLY(lhsclk,lhsvalue);
  			   Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt)))]@vc,
  	 			nv)
    	else
    		begin
    			match v with
    			| Y_VAR(varid) ->
  					let (memv,_) = create_memorized_vars varid in
  					(lhsclk,
  	 				lhsvalue,
  					vt,
  	 				[Y_EQ(lhsclk,c)]@cc,
  	 				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(memv)));
  			     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt)))]@vc,
  	 				[(memv,vt)]@nv)
    			| _ -> raise (InvalidExprssion (expr_to_string expr))
    		end
			end
				
(** --------------------------------------------------------------------- *)

(** S_DELAYBYINIT to yices *)
let delaybyinit_expr_to_ycies expr c v vt cc vc nv ci vi vti cci vci nvi mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
    	if (is_event_type vt) then
  			let (newclk,newval) = create_fresh_vars expr in
  			(Y_VAR(newclk),
  	 		Y_VAR(newval),
  			vt,
  	 		[Y_EQ(Y_VAR(newclk),c)]@cc,
  	 		[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
  			 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt)))]@vc,
  	 		[(newclk,Y_BOOL);(newval,vt)]@nv)
    	else
    		begin
    			match v with
    			| Y_VAR(varid) ->
  					let (newclk,newval) = create_fresh_vars expr and
  					(memv,memv0) = create_memorized_vars varid in
  					(Y_VAR(newclk),
  	 				Y_VAR(newval),
  					vt,
  	 				[Y_EQ(Y_VAR(newclk),c)]@cc@cci,
  	 				[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_VAR(memv)));
  			     Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt)));
  			 						Y_EQ(Y_VAR(memv0),vi)]@vc@vci,
  	 				[(newclk,Y_BOOL);(newval,vt);(memv,vt);(memv0,vt)]@nv@nvi)
    			|_ -> raise (InvalidExprssion (expr_to_string expr))
    		end
			end
		else
			begin
				if (is_event_type vt) then
  			(lhsclk,
  	 		lhsvalue,
  			vt,
  	 		[Y_EQ(lhsclk,c)]@cc,
  	 		[Y_IMPLY(lhsclk,lhsvalue);
  			 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt)))]@vc,
  	 		nv)
    	else
    		begin
    			match v with
    			| Y_VAR(varid) ->
  					let (memv,memv0) = create_memorized_vars varid in
  					(lhsclk,
  	 				lhsvalue,
  					vt,
  	 				[Y_EQ(lhsclk,c)]@cc@cci,
  	 				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(memv)));
  			     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt)));
  			 						Y_EQ(Y_VAR(memv0),vi)]@vc@vci,
  	 				[(memv,vt);(memv0,vt)]@nv@nvi)
    			|_ -> raise (InvalidExprssion (expr_to_string expr))
    		end
			end
		
(** --------------------------------------------------------------------- *)

(** S_DEFAULT to yices *)
let default_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
    	if ((is_event_type vt1) && (is_event_type vt2)) then
  			let (newclk,newval) = create_fresh_vars expr in
  			(Y_VAR(newclk),
  		 	Y_VAR(newval),
  			vt1,
  		 	[Y_EQ(Y_VAR(newclk),Y_OR([c1;c2]))]@cc1@cc2,
  		 	[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
  			 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
  		 	[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    	else if ((is_event_type vt1) && not (is_event_type vt2)) then
    		begin
    			match vt2 with
    			| Y_CONST(ybtype) ->
						begin
							match v2 with
							| Y_CTRUE -> 
								let (newclk,newval) = create_fresh_vars expr in
								(Y_VAR(newclk),
	 							Y_VAR(newval),
								Y_NAMED_TYPED("event"),
	 							[Y_EQ(Y_VAR(newclk),Y_OR([c1;Y_VAR(newclk)]))]@cc1@cc2,
	 							[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
			      		 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
	  						[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
							| Y_CFALSE -> 
								let (newclk,newval) = create_fresh_vars expr in
								(Y_VAR(newclk),
	 							Y_VAR(newval),
								Y_BOOL,
	 							[Y_EQ(Y_VAR(newclk),Y_OR([c1;Y_VAR(newclk)]))]@cc1@cc2,
	 							[Y_IMPLY(Y_VAR(newclk),Y_OR([Y_AND([c1;Y_VAR(newval)]);Y_AND([Y_NOT(c1);Y_EQ(Y_VAR(newval),Y_CFALSE)])]));
			 	 				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
	  						[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
							| _ -> raise (InvalidExprssion (expr_to_string expr))
						end
    			| _ -> 
  					let (newclk,newval) = create_fresh_vars expr in
						(Y_VAR(newclk),
 						Y_VAR(newval),
						vt2,
 						[Y_EQ(Y_VAR(newclk),Y_OR([c1;c2]))]@cc1@cc2,
 						[Y_IMPLY(Y_VAR(newclk),Y_OR([Y_AND([c1;Y_VAR(newval)]);Y_AND([Y_NOT(c1);Y_EQ(Y_VAR(newval),v2)])]));
	 	 				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
						[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
    		end
    	else if (not (is_event_type vt1) && (is_event_type vt2)) then
    		begin
    			match vt1 with
    			| Y_CONST(ybtype) ->
    				begin
							match v1 with
							| Y_CTRUE -> 
								let (newclk,newval) = create_fresh_vars expr in
								(Y_VAR(newclk),
	 							Y_VAR(newval),
								Y_NAMED_TYPED("event"),
	 							[Y_EQ(Y_VAR(newclk),Y_OR([c2;Y_VAR(newclk)]))]@cc1@cc2,
	 							[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
			      		 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
	  						[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
							| Y_CFALSE -> 
								let (newclk,newval) = create_fresh_vars expr in
								(Y_VAR(newclk),
	 							Y_VAR(newval),
								Y_BOOL,
	 							[Y_EQ(Y_VAR(newclk),Y_OR([c2;Y_VAR(newclk)]))]@cc1@cc2,
	 							[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
			 	 				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
	  						[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
							| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| _ -> 
  					let (newclk,newval) = create_fresh_vars expr in
						(Y_VAR(newclk),
 						Y_VAR(newval),
						vt1,
 						[Y_EQ(Y_VAR(newclk),Y_OR([c1;c2]))]@cc1@cc2,
 						[Y_IMPLY(Y_VAR(newclk),Y_OR([Y_AND([c1;Y_EQ(Y_VAR(newval),v1)]);Y_AND([Y_NOT(c1);Y_VAR(newval)])]));
	 	 				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
						[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
    		end
    	else
    		begin 
    			match (vt1,vt2) with
    			| (Y_CONST(_),Y_CONST(_)) ->
    				(Y_NOTHING,
    		 		v1,
    				vt1,
    		 		cc1@cc2,
    		 		vc1@vc2,
    		 		nv1@nv2)
    			
    			| (Y_CONST(_),_) ->
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  		 			Y_VAR(newval),
  					vt2,
  		 			[Y_EQ(Y_VAR(newclk),Y_OR([c2;Y_VAR(newclk)]))]@cc1@cc2,
  		 			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),v1));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
  		  		[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
    			| (_,Y_CONST(_)) ->
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  		 			Y_VAR(newval),
  					vt1,
  		 			[Y_EQ(Y_VAR(newclk),Y_OR([c1;Y_VAR(newclk)]))]@cc1@cc2,
  		 			[Y_IMPLY(Y_VAR(newclk),Y_OR([Y_AND([c1;Y_EQ(Y_VAR(newval),v1)]);Y_AND([Y_NOT(c1);Y_EQ(Y_VAR(newval),v2)])]));
	 	 				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
  		  		[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
    			| (_,_) ->
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  		 	 		Y_VAR(newval),
  					vt1,
  		 	 		[Y_EQ(Y_VAR(newclk),Y_OR([c1;c2]))]@cc1@cc2,
  		 	 		[Y_IMPLY(Y_VAR(newclk),Y_OR([Y_AND([c1;Y_EQ(Y_VAR(newval),v1)]);Y_AND([Y_NOT(c1);Y_EQ(Y_VAR(newval),v2)])]));
  				 	 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
  		 	 		[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
    		end
			end
		else
			begin
				if ((is_event_type vt1) && (is_event_type vt2)) then
    			(lhsclk,
    		 	lhsvalue,
    			vt1,
    		 	[Y_EQ(lhsclk,Y_OR([c1;c2]))]@cc1@cc2,
    		 	[Y_IMPLY(lhsclk,lhsvalue);
    			 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
    		 	nv1@nv2)
    		else if ((is_event_type vt1) && not (is_event_type vt2)) then
      		begin
      			match vt2 with
      			| Y_CONST(ybtype) ->
  						begin
  							match v2 with
  							| Y_CTRUE -> 
									(lhsclk,
		 							lhsvalue,
									vt1,
		 							[Y_EQ(lhsclk,Y_OR([c1;lhsclk]))]@cc1@cc2,
		 							[Y_IMPLY(lhsclk,lhsvalue);
				      		 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
		  						nv1@nv2)
  							| Y_CFALSE -> 
									(lhsclk,
		 							lhsvalue,
									Y_BOOL,
		 							[Y_EQ(lhsclk,Y_OR([c1;lhsclk]))]@cc1@cc2,
		 							[Y_IMPLY(lhsclk,Y_OR([Y_AND([c1;lhsvalue]);Y_AND([Y_NOT(c1);Y_EQ(lhsvalue,Y_CFALSE)])]));
  				 	 			 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
		  						nv1@nv2)
  							| _ -> raise (InvalidExprssion (expr_to_string expr))
  						end
      			| _ -> 
    					(lhsclk,
    		 			lhsvalue,
    					vt2,
    		 			[Y_EQ(lhsclk,Y_OR([c1;c2]))]@cc1@cc2,
    		 			[Y_IMPLY(lhsclk,Y_OR([Y_AND([c1;Y_EQ(lhsvalue,v1)]);Y_AND([Y_NOT(c1);Y_EQ(lhsvalue,v2)])]));
  				 	 	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
    		 			nv1@nv2)
      		end
    		else if (not (is_event_type vt1) && (is_event_type vt2)) then
      		begin
      			match vt1 with
      			| Y_CONST(ybtype) ->
  						begin
  							match v1 with
  							| Y_CTRUE -> 
									(lhsclk,
		 							lhsvalue,
									vt2,
		 							[Y_EQ(lhsclk,Y_OR([c2;lhsclk]))]@cc1@cc2,
		 							[Y_IMPLY(lhsclk,lhsvalue);
				      		 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
		  						nv1@nv2)
  							| Y_CFALSE -> 
									(lhsclk,
		 							lhsvalue,
									Y_BOOL,
		 							[Y_EQ(lhsclk,Y_OR([c2;lhsclk]))]@cc1@cc2,
		 							[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
  				 	 			 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
		  						nv1@nv2)
  							| _ -> raise (InvalidExprssion (expr_to_string expr))
  						end
      			| _ -> 
    					(lhsclk,
    		 			lhsvalue,
    					vt2,
    		 			[Y_EQ(lhsclk,Y_OR([c1;c2]))]@cc1@cc2,
    		 			[Y_IMPLY(lhsclk,Y_OR([Y_AND([c1;Y_EQ(lhsvalue,v1)]);Y_AND([Y_NOT(c1);Y_EQ(lhsvalue,v2)])]));
  				 	 	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
    		 			nv1@nv2)
      		end
    		else
      		begin 
      			match (vt1,vt2) with
      			| (Y_CONST(_),Y_CONST(_)) ->
      				(lhsclk,
      		 		lhsvalue,
      				vt1,
      		 		cc1@cc2,
      		 		[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v1));
  						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
      		 		nv1@nv2)
      			
      			| (Y_CONST(_),_) ->
    					(lhsclk,
    		 			lhsvalue,
    					vt2,
    		 			[Y_EQ(lhsclk,Y_OR([c2;lhsclk]))]@cc1@cc2,
    		 			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v1));
    					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
    		  		nv1@nv2)
      			| (_,Y_CONST(_)) ->
    					(lhsclk,
    		 			lhsvalue,
    					vt1,
    		 			[Y_EQ(lhsclk,Y_OR([c1;lhsclk]))]@cc1@cc2,
    		 			[Y_IMPLY(lhsclk,Y_OR([Y_AND([c1;Y_EQ(lhsvalue,v1)]);Y_AND([Y_NOT(c1);Y_EQ(lhsvalue,v2)])]));
  				 	 	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
    		  		nv1@nv2)
      			| (_,_) ->
    					(lhsclk,
    		 	 		lhsvalue,
    					vt1,
    		 	 		[Y_EQ(lhsclk,Y_OR([c1;c2]))]@cc1@cc2,
    		 	 		[Y_IMPLY(lhsclk,Y_OR([Y_AND([c1;Y_EQ(lhsvalue,v1)]);Y_AND([Y_NOT(c1);Y_EQ(lhsvalue,v2)])]));
    				 	      	Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
    		 	 		nv1@nv2)
      		end
			end
				
(** --------------------------------------------------------------------- *)
	
(** S_WHEN to yices *)
let when_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
    	if (is_event_type vt1) then
    		begin
    			match vt2 with
    			| Y_CONST(_) -> 
    				begin
    					match v2 with
    					| Y_CTRUE ->
  							let (newclk,newval) = create_fresh_vars expr in
  							(Y_VAR(newclk),
  		 	 		 		Y_VAR(newval),
  							vt1,
  		 	 	   		[Y_EQ(Y_VAR(newclk),Y_AND([c1;Y_VAR(newclk)]))]@cc1@cc2,
  		 	 		 		[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
  				       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
  		 	 		 		[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    					| Y_CFALSE ->
    						(Y_CFALSE,Y_NOTHING,Y_NOTYPE,cc1@cc2,vc1@vc2,nv1@nv2)
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| _ ->
    				begin
    					let (newclk,newval) = create_fresh_vars expr in
    					(Y_VAR(newclk),
    			 		Y_VAR(newval),
    					vt1,
    			 		[Y_EQ(Y_VAR(newclk),Y_AND([c1;c2;v2]))]@cc1@cc2,
    			 		[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
    			     Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
    			 		[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    				end
    		end
    	else
    		begin
    			match (vt1,vt2) with
    			| (Y_CONST(_),Y_CONST(_)) ->
    				begin
    					match v2 with
    					| Y_CTRUE ->
  							(Y_NOTHING,
  		 	 		 		v1,
  							vt1,
  		 	 	   		cc1@cc2,
  		 	 		 		vc1@vc2,
  		 	 		 		nv1@nv2)
    					| Y_CFALSE ->
    						(Y_CFALSE,Y_NOTHING,Y_NOTYPE,cc1@cc2,vc1@vc2,nv1@nv2)
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (Y_CONST(cstbty),_) ->
    				begin
    					match v1 with
    					| Y_CTRUE ->
  							let (newclk,newval) = create_fresh_vars expr in
  							(Y_VAR(newclk),
  			 				Y_VAR(newval),
  							Y_NAMED_TYPED("event"),
  			 				[Y_EQ(Y_VAR(newclk),Y_AND([c2;v2]))]@cc1@cc2,
  			 				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
  			         Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
  			 				[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    					| _ ->
  							let (newclk,newval) = create_fresh_vars expr in
  							(Y_VAR(newclk),
  			 				Y_VAR(newval),
  							cstbty,
  			 				[Y_EQ(Y_VAR(newclk),Y_AND([c2;v2]))]@cc1@cc2,
  			 				[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),v1));
  			         Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
  			 				[(newclk,Y_BOOL);(newval,cstbty)]@nv1@nv2)
    				end
    			| (_,Y_CONST(_)) ->
    				begin
    					match v2 with
    					| Y_CTRUE ->
  							let (newclk,newval) = create_fresh_vars expr in
  							(Y_VAR(newclk),
  		 	 		 		Y_VAR(newval),
  							vt1,
  		 	 	   		[Y_EQ(Y_VAR(newclk),Y_AND([c1;Y_VAR(newclk)]))]@cc1@cc2,
  		 	 		 		[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),v1));
  				       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
  		 	 		 		[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
    					| Y_CFALSE ->
    						(Y_CFALSE,Y_NOTHING,Y_NOTYPE,cc1@cc2,vc1@vc2,nv1@nv2)
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (_,_) ->
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  			 		Y_VAR(newval),
  					vt1,
  			 		[Y_EQ(Y_VAR(newclk),Y_AND([c1;c2;v2]))]@cc1@cc2,
  			 		[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),v1));
  			     Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
  			 		[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
    		end
		end
	else
		begin
			if (is_event_type vt1) then
    		begin
    			match vt2 with
    			| Y_CONST(_) -> 
    				begin
    					match v2 with
    					| Y_CTRUE ->
  							(lhsclk,
  		 	 		 		lhsvalue,
  							vt1,
  		 	 	   		[Y_EQ(lhsclk,Y_AND([c1;lhsclk]))]@cc1@cc2,
  		 	 		 		[Y_IMPLY(lhsclk,lhsvalue);
  				       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  		 	 		 		nv1@nv2)
    					| Y_CFALSE ->
								(lhsclk,
  			 				lhsvalue,
  							vt1,
  			 				[Y_EQ(lhsclk,Y_CFALSE)]@cc1@cc2,
  			 				vc1@vc2,
  			 				nv1@nv2)
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| _ ->
  					(lhsclk,
  			 		lhsvalue,
  					vt1,
  			 		[Y_EQ(lhsclk,Y_AND([c1;c2;v2]))]@cc1@cc2,
  			 		[Y_IMPLY(lhsclk,lhsvalue);
  			     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  			 		nv1@nv2)
    		end
    	else
    		begin
    			match (vt1,vt2) with
    			| (Y_CONST(_),Y_CONST(_)) ->
    				begin
    					match v2 with
    					| Y_CTRUE ->
								(lhsclk,
    		 	 		 	lhsvalue,
    						vt1,
    		 	 	   	cc1@cc2,
    		 	 		 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v1));
    				     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
    		 	 		 	nv1@nv2)
    					| Y_CFALSE ->
    						(lhsclk,
    			 			lhsvalue,
    						vt1,
    			 			[Y_EQ(lhsclk,Y_CFALSE)]@cc1@cc2,
    			 			vc1@vc2,
    			 			nv1@nv2)
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (Y_CONST(cstbty),_) ->
    				begin
    					match v1 with
    					| Y_CTRUE ->
  							(lhsclk,
  			 				lhsvalue,
  							Y_NAMED_TYPED("event"),
  			 				[Y_EQ(lhsclk,Y_AND([c2;v2]))]@cc1@cc2,
  			 				[Y_IMPLY(lhsclk,lhsvalue);
  			         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  			 				nv1@nv2)
    					| _ ->
  							(lhsclk,
  			 				lhsvalue,
  							cstbty,
  			 				[Y_EQ(lhsclk,Y_AND([c2;v2]))]@cc1@cc2,
  			 				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v1));
  			         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  			 				nv1@nv2)
    				end
    			| (_,Y_CONST(_)) ->
    				begin
    					match v2 with
    					| Y_CTRUE ->
  							(lhsclk,
  		 	 		 		lhsvalue,
  							vt1,
  		 	 	   		[Y_EQ(lhsclk,Y_AND([c1;lhsclk]))]@cc1@cc2,
  		 	 		 		[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v1));
  				       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  		 	 		 		nv1@nv2)
    					| Y_CFALSE ->
								(lhsclk,
    			 			lhsvalue,
    						vt1,
    			 			[Y_EQ(lhsclk,Y_CFALSE)]@cc1@cc2,
    			 			vc1@vc2,
    			 			nv1@nv2)
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (_,_) ->
  					(lhsclk,
  			 		lhsvalue,
  					vt1,
  			 		[Y_EQ(lhsclk,Y_AND([c1;c2;v2]))]@cc1@cc2,
  			 		[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v1));
  			     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  			 		nv1@nv2)
    		end	
		end
			
(** --------------------------------------------------------------------- *)
	
(** S_UMINUS to yices *)
let uminus_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 mode lhsclk lhsvalue =
	if (is_event_type vt1) then
		raise (InvalidExprssion (expr_to_string expr))
	else
		begin
			match vt1 with
			| Y_BOOL ->
				raise (InvalidExprssion (expr_to_string expr))
			| Y_CONST(ybty) ->
				begin
					match v1 with
					| Y_VAR(const_var_name) ->
						begin
							let const_var_expr = Hashtbls.get_val_const_hashtbl const_var_name in
							match const_var_expr with
    					| (Y_CFALSE | Y_CTRUE) ->
    						raise (InvalidExprssion (expr_to_string expr))
							| Y_CNAT(nat1) ->
								begin
									let cstvalueplus = string_of_int (0 - (int_of_string nat1)) in
            			try
    								begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
    									if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1,vc1,nv1)
    									else
    										(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1,
                  			nv1)
    								end
            			with SymNotFound(smsg) ->
    								begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
    									if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1,vc1,[(const_var,Y_CONST(Y_INT))]@nv1)
    									else
    										(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1,
                  			[(const_var,Y_CONST(Y_INT))]@nv1)
    								end
								end
							| Y_CINT(i1) ->
								begin
									let cstvalueplus = string_of_int (0 - (int_of_string i1)) in
            			try
    								begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
    									if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1,vc1,nv1)
    									else
    										(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1,
                  			nv1)
    								end
            			with SymNotFound(smsg) ->
    								begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
    									if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1,vc1,[(const_var,Y_CONST(Y_INT))]@nv1)
    									else
    										(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1,
                  			[(const_var,Y_CONST(Y_INT))]@nv1)
    								end
								end
							| Y_CREAL(r1) ->
								begin
									let cstvalueplus = string_of_float (0.0 -. (float_of_string r1)) in
            			try
    								begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CREAL(cstvalueplus)) in
    									if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),cc1,vc1,nv1)
    									else
    										(lhsclk,
                  			lhsvalue,
                  			Y_REAL,
                  			cc1,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))]@vc1,
                  			nv1)
    								end
            			with SymNotFound(smsg) ->
    								begin
              				let const_var = create_const_vars (Y_CREAL(cstvalueplus)) in
    									if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),cc1,vc1,[(const_var,Y_CONST(Y_REAL))]@nv1)
    									else
    										(lhsclk,
                  			lhsvalue,
                  			Y_REAL,
                  			cc1,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))]@vc1,
                  			[(const_var,Y_CONST(Y_REAL))]@nv1)
    								end
    						end
    					| Y_CCOMPLEX(r1,i1) ->
    						begin
    							let r_cstvalueplus = string_of_float (0.0 -. (float_of_string r1)) in
    							let i_cstvalueplus = string_of_float (0.0 -. (float_of_string i1)) in
            			try
    								begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CCOMPLEX(r_cstvalueplus,i_cstvalueplus)) in
    									if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),cc1,vc1,nv1)
    									else
    										(lhsclk,
                  			lhsvalue,
                  			Y_COMPLEX,
                  			cc1,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))]@vc1,
                  			nv1)
    								end
            			with SymNotFound(smsg) ->
    								begin
              				let const_var = create_const_vars (Y_CCOMPLEX(r_cstvalueplus,i_cstvalueplus)) in
    									if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),cc1,vc1,[(const_var,Y_CONST(Y_COMPLEX))]@nv1)
    									else
    										(lhsclk,
                  			lhsvalue,
                  			Y_COMPLEX,
                  			cc1,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))]@vc1,
                  			[(const_var,Y_CONST(Y_COMPLEX))]@nv1)
    								end
								end
							| _ -> raise (InvalidExprssion (expr_to_string expr))
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| _ ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "uminus" Y_NOTHING v1 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt1,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1,
  				 	vc1,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "uminus" Y_NOTHING v1 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1)
				end
		end

(** --------------------------------------------------------------------- *)
	
(** S_NOT to yices *)
let not_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
    	if (is_event_type vt1) then
    		(c1,Y_NOT(v1),Y_BOOL,cc1,vc1,nv1)
    	else
    		begin
    			match vt1 with
    			| Y_CONST(_) ->
    				begin
    					match v1 with
    					| Y_CTRUE -> 
    						(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1,vc1,nv1)
    					| Y_CFALSE ->
    						(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1,vc1,nv1)
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| _ ->
    				(c1,Y_NOT(v1),vt1,cc1,vc1,nv1)
    		end
		end
	else
		begin
			if (is_event_type vt1) then
				(lhsclk,
 				lhsvalue,
				Y_BOOL,
	 			[Y_EQ(lhsclk,c1)]@cc1,
	 			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_NOT(v1)));
	     	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1,
	 			nv1)
    	else
    		begin
    			match vt1 with
    			| Y_CONST(_) ->
    				begin
    					match v1 with
    					| Y_CTRUE -> 
								(lhsclk,
         				lhsvalue,
        				Y_BOOL,
        	 			cc1,
        	 			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
        	     	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1,
        	 			nv1)
    					| Y_CFALSE ->
								(lhsclk,
         				lhsvalue,
        				Y_NAMED_TYPED("event"),
        	 			cc1,
        	 			[Y_IMPLY(lhsclk,lhsvalue);
        	     	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1,
        	 			nv1)
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| _ ->
						(lhsclk,
     				lhsvalue,
    				Y_BOOL,
    	 			[Y_EQ(lhsclk,c1)]@cc1,
    	 			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_NOT(v1)));
    	     	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1,
    	 			nv1)
    		end
		end
				
(** --------------------------------------------------------------------- *)

(** S_AND to yices *)
let and_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
    	if ((is_event_type vt1) && (is_event_type vt2)) then
    		let (newclk,newval) = create_fresh_vars expr in
    		(Y_VAR(newclk),
     		Y_VAR(newval),
    		Y_NAMED_TYPED("event"),
     		[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
     		[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
         Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
     		[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    	else if ((is_event_type vt1) && not (is_event_type vt2)) then
    		begin
    			match vt2 with
    			| Y_CONST(ybtype) ->
    				begin
    					match ybtype with
    					| Y_BOOL -> 
    						begin
    							match v2 with
    							| Y_CTRUE -> 
    								let (newclk,newval) = create_fresh_vars expr in
    								(Y_VAR(newclk),
     								Y_VAR(newval),
    								Y_NAMED_TYPED("event"),
     								[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
     								[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
    	      				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
    								[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    							| Y_CFALSE -> 
    								let (newclk,newval) = create_fresh_vars expr in
    								(Y_VAR(newclk),
     								Y_VAR(newval),
    								Y_BOOL,
     								[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
     								[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
    	      				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    								[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
    							| _ -> raise (InvalidExprssion (expr_to_string expr))
    						end
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| _ -> 
    				let (newclk,newval) = create_fresh_vars expr in
    				(Y_VAR(newclk),
      			Y_VAR(newval),
    				Y_BOOL,
      			[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
      			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),v2));
    	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
      			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
    		end
    	else if (not (is_event_type vt1) && (is_event_type vt2)) then
    		begin
    			match vt1 with
    			| Y_CONST(ybtype) ->
    				begin
    					match ybtype with
    					| Y_BOOL -> 
    						begin
    							match v1 with
    							| Y_CTRUE -> 
    								let (newclk,newval) = create_fresh_vars expr in
    								(Y_VAR(newclk),
     								Y_VAR(newval),
    								Y_NAMED_TYPED("event"),
     								[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
     								[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
    	      				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
    								[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    							| Y_CFALSE -> 
    								let (newclk,newval) = create_fresh_vars expr in
    								(Y_VAR(newclk),
     								Y_VAR(newval),
    								Y_BOOL,
     								[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
     								[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
    	      				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    								[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
    							| _ -> raise (InvalidExprssion (expr_to_string expr))
    						end
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| _ -> 
    				let (newclk,newval) = create_fresh_vars expr in
    				(Y_VAR(newclk),
      			Y_VAR(newval),
    				Y_BOOL,
      			[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
      			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),v1));
    	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
      			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
    		end
    	else
    		begin
    			match (vt1,vt2) with
    			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
    				begin
    					match (v1,v2) with
    					| (Y_CTRUE,Y_CTRUE) -> 
    						(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
    					| ((Y_CTRUE,Y_CFALSE) | (Y_CFALSE,Y_CTRUE) | (Y_CFALSE,Y_CFALSE)) -> 
    						(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
    					| _ -> 
    						raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (Y_CONST(ybty1),_) ->
    				begin
    					match v1 with
    					| Y_CFALSE -> 
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
     	 			 		Y_VAR(newval),
    						vt2,
     	 			  	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
     	 			    [Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
    		       	 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
     	 			 		[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
    					| Y_CTRUE ->
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
     	 			 		Y_VAR(newval),
    						vt2,
     	 			  	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),v2));
    		       	 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
     	 			 		[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
    					| _ -> 
    						raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (_,Y_CONST(ybty2)) ->
    				begin
    					match v2 with
    					| Y_CFALSE -> 
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
     	 			 		Y_VAR(newval),
    						vt1,
     	 			  	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
     	 			  	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
    		       	 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
     	 			 		[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
    					| Y_CTRUE ->
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
     	 			 		Y_VAR(newval),
    						vt1,
     	 			  	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
     	 			  	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),v1));
    		       	 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
     	 			 		[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
    					| _ -> 
    						raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (_,_) ->
    				let (newclk,newval) = create_fresh_vars expr in
    				(Y_VAR(newclk),
      			Y_VAR(newval),
    				vt1,
      			[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
      			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_AND([v1;v2])));
    	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
      			[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
    		end
		end
	else
		begin
			if ((is_event_type vt1) && (is_event_type vt2)) then
    		(lhsclk,
     		lhsvalue,
    		Y_NAMED_TYPED("event"),
     		[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
     		[Y_IMPLY(lhsclk,lhsvalue);
         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
     		nv1@nv2)
    	else if ((is_event_type vt1) && not (is_event_type vt2)) then
    		begin
    			match vt2 with
    			| Y_CONST(ybtype) ->
    				begin
    					match ybtype with
    					| Y_BOOL -> 
    						begin
    							match v2 with
    							| Y_CTRUE -> 
    								(lhsclk,
     								lhsvalue,
    								Y_NAMED_TYPED("event"),
     								[Y_EQ(lhsclk,c1)]@cc1@cc2,
     								[Y_IMPLY(lhsclk,lhsvalue);
    	      				 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
    								nv1@nv2)
    							| Y_CFALSE -> 
    								(lhsclk,
     								lhsvalue,
    								Y_BOOL,
     								[Y_EQ(lhsclk,c1)]@cc1@cc2,
     								[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
    	      				 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    								nv1@nv2)
    							| _ -> raise (InvalidExprssion (expr_to_string expr))
    						end
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| _ -> 
    				(lhsclk,
      			lhsvalue,
    				Y_BOOL,
      			[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v2));
    	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
      			nv1@nv2)
    		end
    	else if (not (is_event_type vt1) && (is_event_type vt2)) then
    		begin
    			match vt1 with
    			| Y_CONST(ybtype) ->
    				begin
    					match ybtype with
    					| Y_BOOL -> 
    						begin
    							match v1 with
    							| Y_CTRUE -> 
    								(lhsclk,
     								lhsvalue,
    								Y_NAMED_TYPED("event"),
     								[Y_EQ(lhsclk,c2)]@cc1@cc2,
     								[Y_IMPLY(lhsclk,lhsvalue);
    	      				 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
    								nv1@nv2)
    							| Y_CFALSE -> 
    								(lhsclk,
     								lhsvalue,
    								Y_BOOL,
     								[Y_EQ(lhsclk,c2)]@cc1@cc2,
     								[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
    	      				 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    								nv1@nv2)
    							| _ -> raise (InvalidExprssion (expr_to_string expr))
    						end
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| _ -> 
    				(lhsclk,
      			lhsvalue,
    				Y_BOOL,
      			[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v1));
    	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
      			nv1@nv2)
    		end
    	else
    		begin
    			match (vt1,vt2) with
    			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
    				begin
    					match (v1,v2) with
    					| (Y_CTRUE,Y_CTRUE) -> 
								(lhsclk,
          			lhsvalue,
        				Y_NAMED_TYPED("event"),
          			cc1@cc2,
          			[Y_IMPLY(lhsclk,lhsvalue);
        	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
          			nv1@nv2)
    					| ((Y_CTRUE,Y_CFALSE) | (Y_CFALSE,Y_CTRUE) | (Y_CFALSE,Y_CFALSE)) -> 
								(lhsclk,
          			lhsvalue,
        				Y_BOOL,
          			cc1@cc2,
          			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
        	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
          			nv1@nv2)
    					| _ -> 
    						raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (Y_CONST(ybty1),_) ->
    				begin
    					match v1 with
    					| Y_CFALSE -> 
    						(lhsclk,
     	 			 		lhsvalue,
    						vt2,
     	 			  	[Y_EQ(lhsclk,c2)]@cc1@cc2,
     	 			    [Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
    		       	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
     	 			 		nv1@nv2)
    					| Y_CTRUE ->
    						(lhsclk,
     	 			 		lhsvalue,
    						vt2,
     	 			  	[Y_EQ(lhsclk,c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v2));
    		       	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
     	 			 		nv1@nv2)
    					| _ -> 
    						raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (_,Y_CONST(ybty2)) ->
    				begin
    					match v2 with
    					| Y_CFALSE -> 
    						(lhsclk,
     	 			 		lhsvalue,
    						vt1,
     	 			  	[Y_EQ(lhsclk,c1)]@cc1@cc2,
     	 			  	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
    		       	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
     	 			 		nv1@nv2)
    					| Y_CTRUE ->
    						(lhsclk,
     	 			 		lhsvalue,
    						vt1,
     	 			  	[Y_EQ(lhsclk,c1)]@cc1@cc2,
     	 			  	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v1));
    		       	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
     	 			 		nv1@nv2)
    					| _ -> 
    						raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (_,_) ->
    				(lhsclk,
      			lhsvalue,
    				vt1,
      			[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_AND([v1;v2])));
    	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
      			nv1@nv2)
    		end
		end

(** --------------------------------------------------------------------- *)

(** S_OR to yices *)
let or_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
    	if (((is_event_type vt1) && (is_event_type vt2)) || ((is_event_type vt1) && not (is_event_type vt2)) || 
    			 (not (is_event_type vt1) && (is_event_type vt2))) then
    		begin
    			match (vt1,vt2) with
    			| (Y_CONST(ybty1),_) ->
    				let (newclk,newval) = create_fresh_vars expr in
    				(Y_VAR(newclk),
     				Y_VAR(newval),
    				Y_NAMED_TYPED("event"),
     				[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
     				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
             Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
     				[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    			| (_,Y_CONST(ybty2)) ->
    				let (newclk,newval) = create_fresh_vars expr in
    				(Y_VAR(newclk),
     				Y_VAR(newval),
    				Y_NAMED_TYPED("event"),
     				[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
     				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
             Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
     				[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    			| (_,_) ->
    				let (newclk,newval) = create_fresh_vars expr in
    				(Y_VAR(newclk),
     				Y_VAR(newval),
    				Y_NAMED_TYPED("event"),
     				[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
     				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
             Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
     				[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    		end
    	else
    		begin
    			match (vt1,vt2) with
    			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
    				begin
    					match (v1,v2) with
    					| (Y_CFALSE,Y_CFALSE) -> 
    						(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
    					| _ -> 
    						(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
    				end
    			| (Y_CONST(ybty1),_) ->
    				let (newclk,newval) = create_fresh_vars expr in
    				(Y_VAR(newclk),
      			Y_VAR(newval),
    				vt2,
      			[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
      			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_OR([v1;v2])));
    	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
      			[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
    			| (_,Y_CONST(ybty2)) ->
    				let (newclk,newval) = create_fresh_vars expr in
    				(Y_VAR(newclk),
      			Y_VAR(newval),
    				vt1,
      			[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
      			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_OR([v1;v2])));
    	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
      			[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
    			| (_,_) ->
    				let (newclk,newval) = create_fresh_vars expr in
    				(Y_VAR(newclk),
      			Y_VAR(newval),
    				vt1,
      			[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
      			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_OR([v1;v2])));
    	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
      			[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
    		end
		end
	else
		begin
			if (((is_event_type vt1) && (is_event_type vt2)) || ((is_event_type vt1) && not (is_event_type vt2)) || 
    			 (not (is_event_type vt1) && (is_event_type vt2))) then
    		begin
    			match (vt1,vt2) with
    			| (Y_CONST(ybty1),_) ->
    				(lhsclk,
     				lhsvalue,
    				Y_NAMED_TYPED("event"),
     				[Y_EQ(lhsclk,c2)]@cc1@cc2,
     				[Y_IMPLY(lhsclk,lhsvalue);
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
     				nv1@nv2)
    			| (_,Y_CONST(ybty2)) ->
    				(lhsclk,
     				lhsvalue,
    				Y_NAMED_TYPED("event"),
     				[Y_EQ(lhsclk,c1)]@cc1@cc2,
     				[Y_IMPLY(lhsclk,lhsvalue);
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
     				nv1@nv2)
    			| (_,_) ->
    				(lhsclk,
     				lhsvalue,
    				Y_NAMED_TYPED("event"),
     				[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
     				[Y_IMPLY(lhsclk,lhsvalue);
             Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
     				nv1@nv2)
    		end
    	else
    		begin
    			match (vt1,vt2) with
    			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
    				begin
    					match (v1,v2) with
    					| (Y_CFALSE,Y_CFALSE) -> 
								(lhsclk,
          			lhsvalue,
        				Y_BOOL,
          			cc1@cc2,
          			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
        	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
          			nv1@nv2)
    					| _ -> 
								(lhsclk,
          			lhsvalue,
        				Y_NAMED_TYPED("event"),
          			cc1@cc2,
          			[Y_IMPLY(lhsclk,lhsvalue);
        	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
          			nv1@nv2)
    				end
    			| (Y_CONST(ybty1),_) ->
    				(lhsclk,
      			lhsvalue,
    				vt2,
      			[Y_EQ(lhsclk,c2)]@cc1@cc2,
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_OR([v1;v2])));
    	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
      			nv1@nv2)
    			| (_,Y_CONST(ybty2)) ->
    				(lhsclk,
      			lhsvalue,
    				vt1,
      			[Y_EQ(lhsclk,c1)]@cc1@cc2,
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_OR([v1;v2])));
    	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
      			nv1@nv2)
    			| (_,_) ->
    				(lhsclk,
      			lhsvalue,
    				vt1,
      			[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_OR([v1;v2])));
    	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
      			nv1@nv2)
    		end
		end
			
(** --------------------------------------------------------------------- *)

(** S_XOR to yices *)
let xor_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue =
	if (mode == 0) then
		begin
    	if ((is_event_type vt1) && (is_event_type vt2)) then
    		let (newclk,newval) = create_fresh_vars expr in
    		(Y_VAR(newclk),
     		Y_VAR(newval),
    		Y_BOOL,
     		[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
     		[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
         Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
     		[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
    	else if ((is_event_type vt1) && not (is_event_type vt2)) then
    		begin
    			match vt2 with
    			| Y_CONST(ybtype) ->
    				begin
    					match ybtype with
    					| Y_BOOL -> 
    						begin
    							match v2 with
    							| Y_CFALSE -> 
    								let (newclk,newval) = create_fresh_vars expr in
    								(Y_VAR(newclk),
     								Y_VAR(newval),
    								Y_NAMED_TYPED("event"),
     								[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
     								[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
    	      				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
    								[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    							| Y_CTRUE -> 
    								let (newclk,newval) = create_fresh_vars expr in
    								(Y_VAR(newclk),
     								Y_VAR(newval),
    								Y_BOOL,
     								[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
     								[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
    	      				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    								[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
    							| _ -> raise (InvalidExprssion (expr_to_string expr))
    						end
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| _ -> 
    				let (newclk,newval) = create_fresh_vars expr in
    				(Y_VAR(newclk),
      			Y_VAR(newval),
    				Y_BOOL,
      			[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
      			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_NOT(v2)));
    	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
      			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
    		end
    	else if (not (is_event_type vt1) && (is_event_type vt2)) then
    		begin
    			match vt1 with
    			| Y_CONST(ybtype) ->
    				begin
    					match ybtype with
    					| Y_BOOL -> 
    						begin
    							match v1 with
    							| Y_CFALSE -> 
    								let (newclk,newval) = create_fresh_vars expr in
    								(Y_VAR(newclk),
     								Y_VAR(newval),
    								Y_NAMED_TYPED("event"),
     								[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
     								[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
    	      				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
    								[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    							| Y_CTRUE -> 
    								let (newclk,newval) = create_fresh_vars expr in
    								(Y_VAR(newclk),
     								Y_VAR(newval),
    								Y_BOOL,
     								[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
     								[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
    	      				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    								[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
    							| _ -> raise (InvalidExprssion (expr_to_string expr))
    						end
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| _ -> 
    				let (newclk,newval) = create_fresh_vars expr in
    				(Y_VAR(newclk),
      			Y_VAR(newval),
    				Y_BOOL,
      			[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
      			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_NOT(v1)));
    	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
      			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
    		end
    	else
    		begin
    			match (vt1,vt2) with
    			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
    				begin
    					match (v1,v2) with
    					| ((Y_CTRUE,Y_CTRUE) | (Y_CFALSE,Y_CFALSE)) -> 
    						(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
    					| ((Y_CTRUE,Y_CFALSE) | (Y_CFALSE,Y_CTRUE)) -> 
    						(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
    					| _ -> 
    						raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (Y_CONST(ybty1),_) ->
    				begin
    					match v1 with
    					| Y_CFALSE -> 
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
     	 			 		Y_VAR(newval),
    						vt2,
     	 			  	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),v2));
    		       	 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
     	 			 		[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
    					| Y_CTRUE ->
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
     	 			 		Y_VAR(newval),
    						vt2,
     	 			  	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_NOT(v2)));
    		       	 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
     	 			 		[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
    					| _ -> 
    						raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (_,Y_CONST(ybty2)) ->
    				begin
    					match v2 with
    					| Y_CFALSE -> 
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
     	 			 		Y_VAR(newval),
    						vt1,
     	 			  	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
     	 			  	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),v1));
    		       	 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
     	 			 		[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
    					| Y_CTRUE ->
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
     	 			 		Y_VAR(newval),
    						vt1,
     	 			  	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
     	 			  	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_NOT(v1)));
    		       	 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
     	 			 		[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
    					| _ -> 
    						raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (_,_) ->
    				begin
    					let (newclk,newval) = create_fresh_vars expr in
    					(Y_VAR(newclk),
     	 			 	Y_VAR(newval),
    					vt1,
     	 			  [Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
     	 			  [Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_OR([Y_AND[v1;Y_NOT(v2)];Y_AND[Y_NOT(v1);v2]])));
    		       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
     	 			 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
    				end
    		end
		end
	else
		begin
			if ((is_event_type vt1) && (is_event_type vt2)) then
    		(lhsclk,
     		lhsvalue,
    		Y_BOOL,
     		[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
     		[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
     		nv1@nv2)
    	else if ((is_event_type vt1) && not (is_event_type vt2)) then
    		begin
    			match vt2 with
    			| Y_CONST(ybtype) ->
    				begin
    					match ybtype with
    					| Y_BOOL -> 
    						begin
    							match v2 with
    							| Y_CFALSE -> 
    								(lhsclk,
     								lhsvalue,
    								Y_NAMED_TYPED("event"),
     								[Y_EQ(lhsclk,c1)]@cc1@cc2,
     								[Y_IMPLY(lhsclk,lhsvalue);
    	      				 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
    								nv1@nv2)
    							| Y_CTRUE -> 
    								(lhsclk,
     								lhsvalue,
    								Y_BOOL,
     								[Y_EQ(lhsclk,c1)]@cc1@cc2,
     								[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
    	      				 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    								nv1@nv2)
    							| _ -> raise (InvalidExprssion (expr_to_string expr))
    						end
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| _ -> 
    				(lhsclk,
      			lhsvalue,
    				Y_BOOL,
      			[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_NOT(v2)));
    	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
      			nv1@nv2)
    		end
    	else if (not (is_event_type vt1) && (is_event_type vt2)) then
    		begin
    			match vt1 with
    			| Y_CONST(ybtype) ->
    				begin
    					match ybtype with
    					| Y_BOOL -> 
    						begin
    							match v1 with
    							| Y_CFALSE -> 
    								(lhsclk,
     								lhsvalue,
    								Y_NAMED_TYPED("event"),
     								[Y_EQ(lhsclk,c2)]@cc1@cc2,
     								[Y_IMPLY(lhsclk,lhsvalue);
    	      				 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
    								nv1@nv2)
    							| Y_CTRUE -> 
    								(lhsclk,
     								lhsvalue,
    								Y_BOOL,
     								[Y_EQ(lhsclk,c2)]@cc1@cc2,
     								[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
    	      				 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    								nv1@nv2)
    							| _ -> raise (InvalidExprssion (expr_to_string expr))
    						end
    					| _ -> raise (InvalidExprssion (expr_to_string expr))
    				end
    			| _ -> 
    				(lhsclk,
      			lhsvalue,
    				Y_BOOL,
      			[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_NOT(v1)));
    	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
      			nv1@nv2)
    		end
    	else
    		begin
    			match (vt1,vt2) with
    			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
    				begin
    					match (v1,v2) with
    					| ((Y_CTRUE,Y_CTRUE) | (Y_CFALSE,Y_CFALSE)) -> 
								(lhsclk,
          			lhsvalue,
        				Y_BOOL,
          			cc1@cc2,
          			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
        	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
          			nv1@nv2)
    					| ((Y_CTRUE,Y_CFALSE) | (Y_CFALSE,Y_CTRUE)) -> 
								(lhsclk,
          			lhsvalue,
        				Y_NAMED_TYPED("event"),
          			cc1@cc2,
          			[Y_IMPLY(lhsclk,lhsvalue);
        	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
          			nv1@nv2)
    					| _ -> 
    						raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (Y_CONST(ybty1),_) ->
    				begin
    					match v1 with
    					| Y_CFALSE -> 
    						(lhsclk,
     	 			 		lhsvalue,
    						vt2,
     	 			  	[Y_EQ(lhsclk,c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v2));
    		       	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
     	 			 		nv1@nv2)
    					| Y_CTRUE ->
    						(lhsclk,
     	 			 		lhsvalue,
    						vt2,
     	 			  	[Y_EQ(lhsclk,c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_NOT(v2)));
    		       	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
     	 			 		nv1@nv2)
    					| _ -> 
    						raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (_,Y_CONST(ybty2)) ->
    				begin
    					match v2 with
    					| Y_CFALSE -> 
    						(lhsclk,
     	 			 		lhsvalue,
    						vt1,
     	 			  	[Y_EQ(lhsclk,c1)]@cc1@cc2,
     	 			  	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v1));
    		       	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
     	 			 		nv1@nv2)
    					| Y_CTRUE ->
    						(lhsclk,
     	 			 		lhsvalue,
    						vt1,
     	 			  	[Y_EQ(lhsclk,c1)]@cc1@cc2,
     	 			  	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_NOT(v1)));
    		       	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
     	 			 		nv1@nv2)
    					| _ -> 
    						raise (InvalidExprssion (expr_to_string expr))
    				end
    			| (_,_) ->
    				begin
    					(lhsclk,
     	 			 	lhsvalue,
    					vt1,
     	 			  [Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
     	 			  [Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_OR([Y_AND[v1;Y_NOT(v2)];Y_AND[Y_NOT(v1);v2]])));
    		       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
     	 			 	nv1@nv2)
    				end
    		end
		end
		
(** --------------------------------------------------------------------- *)
	
(** S_EQ to yices *)
let eq_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue =
	if ((is_event_type vt1) && (is_event_type vt2)) then
		if (mode == 0) then
  		let (newclk,newval) = create_fresh_vars expr in
  		(Y_VAR(newclk),
   		Y_VAR(newval),
  		Y_NAMED_TYPED("event"),
   		[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
   		[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
   		[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
		else
			(lhsclk,
   		lhsvalue,
  		Y_NAMED_TYPED("event"),
   		[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
   		[Y_IMPLY(lhsclk,lhsvalue);
       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
   		nv1@nv2)
	else if ((is_event_type vt1) && not (is_event_type vt2)) then
		begin
			match vt2 with
			| Y_CONST(ybtype) ->
				begin
					match v2 with
					| Y_CTRUE -> 
						if (mode == 0) then
  						let (newclk,newval) = create_fresh_vars expr in
  						(Y_VAR(newclk),
   						Y_VAR(newval),
  						Y_NAMED_TYPED("event"),
   						[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
   					  [Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
  	      		 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
  						[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
						else
							(lhsclk,
   						lhsvalue,
  						Y_NAMED_TYPED("event"),
   						[Y_EQ(lhsclk,c1)]@cc1@cc2,
   					  [Y_IMPLY(lhsclk,lhsvalue);
  	      		 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  						nv1@nv2)
					| Y_CFALSE -> 
						if (mode == 0) then
  						let (newclk,newval) = create_fresh_vars expr in
  						(Y_VAR(newclk),
   						Y_VAR(newval),
  						Y_BOOL,
   						[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
   						[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
  	      		 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  						[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						else
							(lhsclk,
   						lhsvalue,
  						Y_BOOL,
   						[Y_EQ(lhsclk,c1)]@cc1@cc2,
   						[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
  	      		 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  						nv1@nv2)
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| Y_BOOL -> 
				if (mode == 0) then
  				let (newclk,newval) = create_fresh_vars expr in
  				(Y_VAR(newclk),
    			Y_VAR(newval),
  				Y_BOOL,
    			[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
    			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),v2));
  	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
    			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				else
					(lhsclk,
    			lhsvalue,
  				Y_BOOL,
    			[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v2));
  	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
    			nv1@nv2)
			| _ -> raise (InvalidExprssion (expr_to_string expr))
		end
	else if (not (is_event_type vt1) && (is_event_type vt2)) then
		begin
			match vt1 with
			| Y_CONST(ybtype) ->
				begin
					match v1 with
					| Y_CTRUE -> 
						if (mode == 0) then
  						let (newclk,newval) = create_fresh_vars expr in
  						(Y_VAR(newclk),
   						Y_VAR(newval),
  						Y_NAMED_TYPED("event"),
   						[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
   						[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
  	      		 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
  						[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
						else
							(lhsclk,
   						lhsvalue,
  						Y_NAMED_TYPED("event"),
   						[Y_EQ(lhsclk,c2)]@cc1@cc2,
   						[Y_IMPLY(lhsclk,lhsvalue);
  	      		 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  						nv1@nv2)
					| Y_CFALSE -> 
						if (mode == 0) then
  						let (newclk,newval) = create_fresh_vars expr in
  						(Y_VAR(newclk),
   						Y_VAR(newval),
  						Y_BOOL,
   						[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
   						[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
  	      		 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  						[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						else
							(lhsclk,
   						lhsvalue,
  						Y_BOOL,
   						[Y_EQ(lhsclk,c2)]@cc1@cc2,
   						[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
  	      		 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  						nv1@nv2)
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| Y_BOOL -> 
				if (mode == 0) then
  				let (newclk,newval) = create_fresh_vars expr in
  				(Y_VAR(newclk),
    			Y_VAR(newval),
  				Y_BOOL,
    			[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
    			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),v1));
  	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
    			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				else
					(lhsclk,
    			lhsvalue,
  				Y_BOOL,
    			[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,v1));
  	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
    			nv1@nv2)
			| _ -> raise (InvalidExprssion (expr_to_string expr))
		end
	else
		begin
			match (vt1,vt2) with
			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
				begin
					if ((compare v1 v2) == 0) then 
						begin
  						if (mode == 0) then
  							(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
  						else
  							(lhsclk,
          			lhsvalue,
        				Y_NAMED_TYPED("event"),
          			cc1@cc2,
          			[Y_IMPLY(lhsclk,lhsvalue);
        	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
          			nv1@nv2)
						end
					else 
						begin
							if (mode == 0) then
								(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
							else
								(lhsclk,
          			lhsvalue,
        				Y_BOOL,
          			cc1@cc2,
          			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
        	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
          			nv1@nv2)
						end
				end
			| (Y_CONST(ybty1),Y_BOOL) ->
				if (mode == 0) then
  				let (newclk,newval) = create_fresh_vars expr in
  				(Y_VAR(newclk),
    			Y_VAR(newval),
  				Y_BOOL,
    			[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
    			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_EQ(v1,v2)));
  	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				else
					(lhsclk,
    			lhsvalue,
  				Y_BOOL,
    			[Y_EQ(lhsclk,c2)]@cc1@cc2,
    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_EQ(v1,v2)));
  	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    			nv1@nv2)
			| (Y_BOOL,Y_CONST(ybty2)) ->
				if (mode == 0) then
  				let (newclk,newval) = create_fresh_vars expr in
  				(Y_VAR(newclk),
    			Y_VAR(newval),
  				Y_BOOL,
    			[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
    			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_EQ(v1,v2)));
  	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				else
					(lhsclk,
    			lhsvalue,
  				Y_BOOL,
    			[Y_EQ(lhsclk,c1)]@cc1@cc2,
    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_EQ(v1,v2)));
  	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    			nv1@nv2)
			| (Y_BOOL,Y_BOOL) ->
				begin
					if (mode == 0) then
						begin
    					let (newclk,newval) = create_fresh_vars expr in
    					if ((compare v1 v2) == 0) then
    						(Y_VAR(newclk),
     	 			 		Y_VAR(newval),
    						Y_NAMED_TYPED("event"),
     	 			  	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
    		       	 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
     	 			 		[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
    					else
    						(Y_VAR(newclk),
     	 			 		Y_VAR(newval),
    						Y_BOOL,
     	 			  	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_EQ(v1,v2)));
    		       	 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
     	 			 		[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					 end
					else
						begin
    					if ((compare v1 v2) == 0) then
    						(lhsclk,
     	 			 		lhsvalue,
    						Y_NAMED_TYPED("event"),
     	 			  	[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(lhsclk,lhsvalue);
    		       	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
     	 			 		nv1@nv2)
    					else
    						(lhsclk,
     	 			 		lhsvalue,
    						Y_BOOL,
     	 			  	[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_EQ(v1,v2)));
    		       	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
     	 			 		nv1@nv2)
						end
				end
			| (Y_CONST(ybty1),_) ->
				begin
  				if (mode == 0) then
    				(* use uninterpreted function *)
    				let (newclk,newval) = create_uninterpreted_vars expr "eq" v1 v2 in
    				(Y_VAR(newclk),
      			Y_VAR(newval),
    				Y_BOOL,
      			[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
      			vc1@vc2,
      			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
  				else
  					let (newclk,newval) = create_uninterpreted_vars expr "eq" v1 v2 in
    				(lhsclk,
      			lhsvalue,
    				Y_BOOL,
      			[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
      		   Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
      			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				end
			| (_,Y_CONST(ybty2)) ->
				begin
  				if (mode == 0) then
    				(* use uninterpreted function *)
    				let (newclk,newval) = create_uninterpreted_vars expr "eq" v1 v2 in
    				(Y_VAR(newclk),
      			Y_VAR(newval),
    				Y_BOOL,
      			[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
      			vc1@vc2,
      			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
  				else
  					let (newclk,newval) = create_uninterpreted_vars expr "eq" v1 v2 in
    				(lhsclk,
      			lhsvalue,
    				Y_BOOL,
      			[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
      			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
      		   Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
      			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				end
			| (_,_) ->
				begin
					if ((compare v1 v2) == 0) then
						begin
							if (mode == 0) then
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
     	 			 		Y_VAR(newval),
    						Y_NAMED_TYPED("event"),
     	 			  	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
    		       	 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
     	 			 		[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
							else
								(lhsclk,
     	 			 		lhsvalue,
    						Y_NAMED_TYPED("event"),
     	 			  	[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(lhsclk,lhsvalue);
    		       	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
     	 			 		nv1@nv2)
						end
					else
						begin
							if (mode == 0) then
    						(* use uninterpreted function *)
    						let (newclk,newval) = create_uninterpreted_vars expr "eq" v1 v2 in
    						(Y_VAR(newclk),
     	 			 		Y_VAR(newval),
    						Y_BOOL,
     	 			  	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
     	 			  	vc1@vc2,
     	 			  	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						 else
								let (newclk,newval) = create_uninterpreted_vars expr "eq" v1 v2 in
        				(lhsclk,
          			lhsvalue,
        				Y_BOOL,
          			[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
          			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
          		   Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
          			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					 end
				end
		end
		
(** --------------------------------------------------------------------- *)

(** S_DIFF to yices *)
let diff_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue = 
	if ((is_event_type vt1) && (is_event_type vt2)) then
		if (mode == 0) then
  		let (newclk,newval) = create_fresh_vars expr in
  		(Y_VAR(newclk),
   		Y_VAR(newval),
  		Y_BOOL,
   		[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
   		[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
  	   Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  		[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
		else
			(lhsclk,
   		lhsvalue,
  		Y_BOOL,
   		[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
   		[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
  	   Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  		nv1@nv2)
	else if ((is_event_type vt1) && not (is_event_type vt2)) then
		begin
			match vt2 with
			| Y_CONST(ybtype) ->
				begin
					match v2 with
					| Y_CFALSE -> 
						if (mode == 0) then
  						let (newclk,newval) = create_fresh_vars expr in
  						(Y_VAR(newclk),
   						Y_VAR(newval),
  						Y_NAMED_TYPED("event"),
   						[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
   						[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
  	      		 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
  						[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
						else
							(lhsclk,
   						lhsvalue,
  						Y_NAMED_TYPED("event"),
   						[Y_EQ(lhsclk,c1)]@cc1@cc2,
   						[Y_IMPLY(lhsclk,lhsvalue);
  	      		 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
  						nv1@nv2)
					| Y_CTRUE -> 
						if (mode == 0) then
  						let (newclk,newval) = create_fresh_vars expr in
  						(Y_VAR(newclk),
   						Y_VAR(newval),
  						Y_BOOL,
   						[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
   						[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
  	      		 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  						[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						else
							(lhsclk,
   						lhsvalue,
  						Y_BOOL,
   						[Y_EQ(lhsclk,c1)]@cc1@cc2,
   						[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
  	      		 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  						nv1@nv2)
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| Y_BOOL -> 
				if (mode == 0) then
  				let (newclk,newval) = create_fresh_vars expr in
  				(Y_VAR(newclk),
    			Y_VAR(newval),
  				Y_BOOL,
    			[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
    			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_NOT(v2)));
  	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
    			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				else
					(lhsclk,
    			lhsvalue,
  				Y_BOOL,
    			[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_NOT(v2)));
  	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
    			nv1@nv2)
			| _ -> raise (InvalidExprssion (expr_to_string expr))
		end
	else if (not (is_event_type vt1) && (is_event_type vt2)) then
		begin
			match vt1 with
			| Y_CONST(ybtype) ->
				begin
					match v1 with
					| Y_CFALSE -> 
						if (mode == 0) then
  						let (newclk,newval) = create_fresh_vars expr in
  						(Y_VAR(newclk),
   						Y_VAR(newval),
  						Y_NAMED_TYPED("event"),
   						[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
   						[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
  	      		 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
  						[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
						else
							(lhsclk,
   						lhsvalue,
  						Y_NAMED_TYPED("event"),
   						[Y_EQ(lhsclk,c2)]@cc1@cc2,
   						[Y_IMPLY(lhsclk,lhsvalue);
  	      		 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  						nv1@nv2)
					| Y_CTRUE -> 
						if (mode == 0) then
  						let (newclk,newval) = create_fresh_vars expr in
  						(Y_VAR(newclk),
   						Y_VAR(newval),
  						Y_BOOL,
   						[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
   						[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
  	      		 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  						[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						else
							(lhsclk,
   						lhsvalue,
  						Y_BOOL,
   						[Y_EQ(lhsclk,c2)]@cc1@cc2,
   						[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
  	      		 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  						nv1@nv2)
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| Y_BOOL -> 
				if (mode == 0) then
  				let (newclk,newval) = create_fresh_vars expr in
  				(Y_VAR(newclk),
    			Y_VAR(newval),
  				Y_BOOL,
    			[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
    			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_NOT(v1)));
  	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt1)))]@vc1@vc2,
    			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				else
					(lhsclk,
    			lhsvalue,
  				Y_BOOL,
    			[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_NOT(v1)));
  	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
    			nv1@nv2)
			| _ -> raise (InvalidExprssion (expr_to_string expr))
		end
	else
		begin
			match (vt1,vt2) with
			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
				begin
					if ((compare v1 v2) == 0) then 
						if (mode == 0) then
							(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),[],[],[])
						else
							(lhsclk,
        			lhsvalue,
      				Y_BOOL,
        			cc1@cc2,
        			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
      	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
        			nv1@nv2)
					else 
						if (mode == 0) then
							(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),[],[],[])
						else
							(lhsclk,
        			lhsvalue,
      				Y_NAMED_TYPED("event"),
        			cc1@cc2,
        			[Y_IMPLY(lhsclk,lhsvalue);
      	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
        			nv1@nv2)
				end
			| (Y_CONST(ybty1),Y_BOOL) ->
				if (mode == 0) then
  				let (newclk,newval) = create_fresh_vars expr in
  				(Y_VAR(newclk),
    			Y_VAR(newval),
  				Y_BOOL,
    			[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
    			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_DIFF(v1,v2)));
  	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				else
					(lhsclk,
    			lhsvalue,
  				Y_BOOL,
    			[Y_EQ(lhsclk,c2)]@cc1@cc2,
    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_DIFF(v1,v2)));
  	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    			nv1@nv2)
			| (Y_BOOL,Y_CONST(ybty2)) ->
				if (mode == 0) then
  				let (newclk,newval) = create_fresh_vars expr in
  				(Y_VAR(newclk),
    			Y_VAR(newval),
  				Y_BOOL,
    			[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
    			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_DIFF(v1,v2)));
  	       Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				else
					(lhsclk,
    			lhsvalue,
  				Y_BOOL,
    			[Y_EQ(lhsclk,c1)]@cc1@cc2,
    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_DIFF(v1,v2)));
  	       Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    			nv1@nv2)
			| (Y_BOOL,Y_BOOL) ->
				begin
					if (mode == 0) then
						begin
    					let (newclk,newval) = create_fresh_vars expr in
    					if ((compare v1 v2) == 0) then
    						(Y_VAR(newclk),
     						Y_VAR(newval),
    						Y_BOOL,
     						[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
     						[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
    		     		 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
      					[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
    					else
    						(Y_VAR(newclk),
     	 			 		Y_VAR(newval),
    						Y_BOOL,
     	 			  	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_DIFF(v1,v2)));
    		       	 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
     	 			 		[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						end
					else 
						begin
    					if ((compare v1 v2) == 0) then
    						(lhsclk,
     						lhsvalue,
    						Y_BOOL,
     						[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
     						[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
    		     		 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
      					nv1@nv2)
    					else
    						(lhsclk,
     	 			 		lhsvalue,
    						Y_BOOL,
     	 			  	[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
     	 			  	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_DIFF(v1,v2)));
    		       	 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
     	 			 		nv1@nv2)
						end
				end
			| (Y_CONST(ybty1),_) ->
				if (mode == 0) then
  				(* use uninterpreted function *)
  				let (newclk,newval) = create_uninterpreted_vars expr "diff" v1 v2 in
  				(Y_VAR(newclk),
    			Y_VAR(newval),
  				Y_BOOL,
    			[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
    			vc1@vc2,
    			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				else
					let (newclk,newval) = create_uninterpreted_vars expr "diff" v1 v2 in
  				(lhsclk,
    			lhsvalue,
  				Y_BOOL,
    			[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
    		   Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
			| (_,Y_CONST(ybty2)) ->
				if (mode == 0) then
  				(* use uninterpreted function *)
  				let (newclk,newval) = create_uninterpreted_vars expr "diff" v1 v2 in
  				(Y_VAR(newclk),
    			Y_VAR(newval),
  				Y_BOOL,
    			[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
    			vc1@vc2,
    			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				else
					let (newclk,newval) = create_uninterpreted_vars expr "diff" v1 v2 in
  				(lhsclk,
    			lhsvalue,
  				Y_BOOL,
    			[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
    		   Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
			| (_,_) ->
				begin
					if ((compare v1 v2) == 0) then
						if (mode == 0) then
  						let (newclk,newval) = create_fresh_vars expr in
  						(Y_VAR(newclk),
   						Y_VAR(newval),
  						Y_BOOL,
   						[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
   						[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
  		     		 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    					[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						else
							(lhsclk,
   						lhsvalue,
  						Y_BOOL,
   						[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
   						[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
  		     		 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    					nv1@nv2)
					else
						if (mode == 0) then
  						(* use uninterpreted function *)
  						let (newclk,newval) = create_uninterpreted_vars expr "diff" v1 v2 in
  						(Y_VAR(newclk),
   	 			 		Y_VAR(newval),
  						Y_BOOL,
   	 			  	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
   	 			  	vc1@vc2,
   	 			  	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						else
							let (newclk,newval) = create_uninterpreted_vars expr "diff" v1 v2 in
      				(lhsclk,
        			lhsvalue,
      				Y_BOOL,
        			[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
        			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
        		   Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
        			[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				end
		end

(** --------------------------------------------------------------------- *)

(** S_GT to yices *)
let gt_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue = 
	if ((is_event_type vt1) && (is_event_type vt2)) then
		begin
			if (mode == 0) then
				let (newclk,newval) = create_fresh_vars expr in
				(Y_VAR(newclk),
				Y_VAR(newval),
				Y_BOOL,
				[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
				[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
				[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
			else 
				(lhsclk,
				lhsvalue,
				Y_BOOL,
				[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
				 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
				nv1@nv2)
		end
	else if ((is_event_type vt1) && not (is_event_type vt2)) then
		begin
			match vt2 with
			| Y_CONST(ybtype) ->
				begin
					match v2 with
					| Y_CFALSE -> 
						begin
							if (mode == 0) then
								let (newclk,newval) = create_fresh_vars expr in
								(Y_VAR(newclk),
				 				Y_VAR(newval),
								Y_NAMED_TYPED("event"),
				 				[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
				 				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
						     Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				  			[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
							else
								(lhsclk,
				 				lhsvalue,
								Y_NAMED_TYPED("event"),
				 				[Y_EQ(lhsclk,c1)]@cc1@cc2,
				 				[Y_IMPLY(lhsclk,lhsvalue);
						     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				  			nv1@nv2)
						end
					| Y_CTRUE -> 
						begin
							if (mode == 0) then
  							let (newclk,newval) = create_fresh_vars expr in
  							(Y_VAR(newclk),
  				 			Y_VAR(newval),
  							Y_BOOL,
  				 			[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
  						   Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				  		[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
							else
								(lhsclk,
				 				lhsvalue,
								Y_BOOL,
				 				[Y_EQ(lhsclk,c1)]@cc1@cc2,
				 				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
						     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
				  			nv1@nv2)
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| Y_BOOL -> 
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_GT(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
		 				lhsvalue,
						Y_BOOL,
		 				[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
		 				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_GT(v1,v2)));
				     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
		  			nv1@nv2)
				end
			| _ -> raise (InvalidExprssion (expr_to_string expr))
		end
	else if (not (is_event_type vt1) && (is_event_type vt2)) then
		begin
			match vt1 with
			| Y_CONST(ybtype) ->
				begin
					match v1 with
					| (Y_CTRUE | Y_CFALSE) -> 
						begin
							if (mode == 0) then
  							let (newclk,newval) = create_fresh_vars expr in
  							(Y_VAR(newclk),
  				 			Y_VAR(newval),
  							Y_BOOL,
  				 			[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
  						   Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				  		[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
							else
  							(lhsclk,
  				 			lhsvalue,
  							Y_BOOL,
  				 			[Y_EQ(lhsclk,c2)]@cc1@cc2,
  				 			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
  						   Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				  		nv1@nv2)
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| Y_BOOL -> 
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_GT(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_GT(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| _ -> raise (InvalidExprssion (expr_to_string expr))
		end
	else
		begin
			match (vt1,vt2) with
			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
				begin
					match (v1,v2) with
					| (Y_CTRUE,Y_CFALSE) -> 
						if (mode == 0) then
							(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
						else
							(lhsclk,
    				 	lhsvalue,
    					Y_NAMED_TYPED("event"),
    				 	cc1@cc2,
    				 	[Y_IMPLY(lhsclk,lhsvalue);
    					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
    				 	nv1@nv2)
					| ((Y_CTRUE,Y_CTRUE) | (Y_CFALSE,Y_CTRUE) | (Y_CFALSE,Y_CFALSE)) -> 
						if (mode == 0) then
							(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
						else
							(lhsclk,
    				 	lhsvalue,
    					Y_BOOL,
    				 	cc1@cc2,
    				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
    					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    				 	nv1@nv2)
					| (Y_VAR(const1),Y_VAR(const2)) ->
						begin
							let const_expr1 = Hashtbls.get_val_const_hashtbl const1 and
									const_expr2 = Hashtbls.get_val_const_hashtbl const2 in
							match (const_expr1,const_expr2) with
							| (Y_CNAT(nat1),Y_CNAT(nat2)) ->
								if ((compare (int_of_string nat1) (int_of_string nat2)) > 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							| (Y_CNAT(nat1),Y_CINT(i2)) ->
								if ((compare (int_of_string nat1) (int_of_string i2)) > 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							| (Y_CINT(i1),Y_CNAT(nat2)) ->
								if ((compare (int_of_string i1) (int_of_string nat2)) > 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							| (Y_CINT(i1),Y_CINT(i2)) ->
								if ((compare (int_of_string i1) (int_of_string i2)) > 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							
							| (Y_CREAL(r1),Y_CREAL(r2)) ->
								if ((compare (float_of_string r1) (float_of_string r2)) > 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							
							| (Y_CCHAR(c1),Y_CCHAR(c2)) ->
								let char1 = String.get c1 0 and
								    char2 = String.get c2 0 in
								if ((compare char1 char2) > 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							
							| (Y_CSTRING(str1),Y_CSTRING(str2)) ->
								begin
									match ybty1 with
									| Y_NAMED_TYPED(strtype) ->
										begin
      								if ((compare str1 str2) > 0) then
      									begin
      										if (mode == 0) then
      											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
      										else
      											(lhsclk,
                  				 	lhsvalue,
                  					Y_NAMED_TYPED("event"),
                  				 	cc1@cc2,
                  				 	[Y_IMPLY(lhsclk,lhsvalue);
                  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
                  				 	nv1@nv2)
      									end
      								else
      									begin
      										if (mode == 0) then
      											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
      										else
      											(lhsclk,
                  				 	lhsvalue,
                  					Y_BOOL,
                  				 	cc1@cc2,
                  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
                  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
                  				 	nv1@nv2)
      									end
										end
									| _ -> (Y_NOTHING,Y_NOTHING,Y_NOTYPE,[],[],[])
								end
							| _ -> raise (InvalidExprssion (expr_to_string expr))
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| (Y_CONST(ybty1),Y_BOOL) ->
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_GT(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_GT(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| (Y_BOOL,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_GT(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_GT(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| (Y_BOOL,Y_BOOL) ->
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_GT(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_GT(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| (Y_CONST(ybty1),_) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "gt" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "gt" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				end
			| (_,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "gt" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "gt" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				end
			| (_,_) ->
				begin
					if ((compare v1 v2) == 0) then
						begin
							if (mode == 0) then
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
    				 		Y_VAR(newval),
    						Y_BOOL,
    				 		[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 		[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
    						 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    				  	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
							else
								(lhsclk,
    				 		lhsvalue,
    						Y_BOOL,
    				 		[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 		[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
    						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    				  	nv1@nv2)
						end
					else
						begin
							if (mode == 0) then
    						(* use uninterpreted function *)
    						let (newclk,newval) = create_uninterpreted_vars expr "gt" v1 v2 in
    						(Y_VAR(newclk),
    				 	 	Y_VAR(newval),
    						Y_BOOL,
    				 	 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 	 	vc1@vc2,
    				 	 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
							else
								let (newclk,newval) = create_uninterpreted_vars expr "gt" v1 v2 in
    						(lhsclk,
      				 	lhsvalue,
      					Y_BOOL,
      				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
      				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
    						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
      				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						end	
					end
			end
			
(** --------------------------------------------------------------------- *)

(** S_GTE to yices *)
let gte_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue = 
	if ((is_event_type vt1) && (is_event_type vt2)) then
		begin
			if (mode == 0) then
				let (newclk,newval) = create_fresh_vars expr in
				(Y_VAR(newclk),
				Y_VAR(newval),
				Y_NAMED_TYPED("event"),
				[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
			else 
				(lhsclk,
				lhsvalue,
				Y_NAMED_TYPED("event"),
				[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
				[Y_IMPLY(lhsclk,lhsvalue);
				 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				nv1@nv2)
		end
	else if ((is_event_type vt1) && not (is_event_type vt2)) then
		begin
			match vt2 with
			| Y_CONST(ybtype) ->
				begin
					match v2 with
					| (Y_CFALSE | Y_CTRUE) -> 
						begin
							if (mode == 0) then
								let (newclk,newval) = create_fresh_vars expr in
								(Y_VAR(newclk),
				 				Y_VAR(newval),
								Y_NAMED_TYPED("event"),
				 				[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
				 				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
						     Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				  			[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
							else
								(lhsclk,
				 				lhsvalue,
								Y_NAMED_TYPED("event"),
				 				[Y_EQ(lhsclk,c1)]@cc1@cc2,
				 				[Y_IMPLY(lhsclk,lhsvalue);
						     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				  			nv1@nv2)
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| Y_BOOL -> 
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_GTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
		 				lhsvalue,
						Y_BOOL,
		 				[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
		 				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_GTE(v1,v2)));
				     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
		  			nv1@nv2)
				end
			| _ -> raise (InvalidExprssion (expr_to_string expr))
		end
	else if (not (is_event_type vt1) && (is_event_type vt2)) then
		begin
			match vt1 with
			| Y_CONST(ybtype) ->
				begin
					match v1 with
					| Y_CTRUE -> 
						begin
							if (mode == 0) then
  							let (newclk,newval) = create_fresh_vars expr in
								(Y_VAR(newclk),
				 				Y_VAR(newval),
								Y_NAMED_TYPED("event"),
				 				[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
				 				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
						     Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				  			[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
							else
  							(lhsclk,
				 				lhsvalue,
								Y_NAMED_TYPED("event"),
				 				[Y_EQ(lhsclk,c2)]@cc1@cc2,
				 				[Y_IMPLY(lhsclk,lhsvalue);
						     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				  			nv1@nv2)
						end
					| Y_CFALSE ->
						if (mode == 0) then
							let (newclk,newval) = create_fresh_vars expr in
    					(Y_VAR(newclk),
    				 	Y_VAR(newval),
    					Y_BOOL,
    				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
    				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
    					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						else
							(lhsclk,
			 				lhsvalue,
							Y_BOOL,
			 				[Y_EQ(lhsclk,c2)]@cc1@cc2,
			 				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
					     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
			  			nv1@nv2)
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| Y_BOOL -> 
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_GTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_GTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| _ -> raise (InvalidExprssion (expr_to_string expr))
		end
	else
		begin
			match (vt1,vt2) with
			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
				begin
					match (v1,v2) with
					| ((Y_CTRUE,Y_CFALSE) | (Y_CTRUE,Y_CTRUE) | (Y_CFALSE,Y_CFALSE)) -> 
						if (mode == 0) then
							(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
						else
							(lhsclk,
    				 	lhsvalue,
    					Y_NAMED_TYPED("event"),
    				 	cc1@cc2,
    				 	[Y_IMPLY(lhsclk,lhsvalue);
    					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
    				 	nv1@nv2)
					| (Y_CFALSE,Y_CTRUE) -> 
						if (mode == 0) then
							(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
						else
							(lhsclk,
    				 	lhsvalue,
    					Y_BOOL,
    				 	cc1@cc2,
    				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
    					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    				 	nv1@nv2)
					| (Y_VAR(const1),Y_VAR(const2)) ->
						begin
							let const_expr1 = Hashtbls.get_val_const_hashtbl const1 and
									const_expr2 = Hashtbls.get_val_const_hashtbl const2 in
							match (const_expr1,const_expr2) with
							| (Y_CNAT(nat1),Y_CNAT(nat2)) ->
								if ((compare (int_of_string nat1) (int_of_string nat2)) >= 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							| (Y_CNAT(nat1),Y_CINT(i2)) ->
								if ((compare (int_of_string nat1) (int_of_string i2)) >= 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							| (Y_CINT(i1),Y_CNAT(nat2)) ->
								if ((compare (int_of_string i1) (int_of_string nat2)) >= 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							| (Y_CINT(i1),Y_CINT(i2)) ->
								if ((compare (int_of_string i1) (int_of_string i2)) >= 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							
							| (Y_CREAL(r1),Y_CREAL(r2)) ->
								if ((compare (float_of_string r1) (float_of_string r2)) >= 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							
							| (Y_CCHAR(c1),Y_CCHAR(c2)) ->
								let char1 = String.get c1 0 and
								    char2 = String.get c2 0 in
								if ((compare char1 char2) >= 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							
							| (Y_CSTRING(str1),Y_CSTRING(str2)) ->
								begin
									match ybty1 with
									| Y_NAMED_TYPED(strtype) ->
										begin
      								if ((compare str1 str2) >= 0) then
      									begin
      										if (mode == 0) then
      											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
      										else
      											(lhsclk,
                  				 	lhsvalue,
                  					Y_NAMED_TYPED("event"),
                  				 	cc1@cc2,
                  				 	[Y_IMPLY(lhsclk,lhsvalue);
                  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
                  				 	nv1@nv2)
      									end
      								else
      									begin
      										if (mode == 0) then
      											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
      										else
      											(lhsclk,
                  				 	lhsvalue,
                  					Y_BOOL,
                  				 	cc1@cc2,
                  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
                  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
                  				 	nv1@nv2)
      									end
										end
									| _ -> (Y_NOTHING,Y_NOTHING,Y_NOTYPE,[],[],[])
								end
							| _ -> raise (InvalidExprssion (expr_to_string expr))
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| (Y_CONST(ybty1),Y_BOOL) ->
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_GTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_GTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| (Y_BOOL,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_GTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_GTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| (Y_BOOL,Y_BOOL) ->
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_GTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_GTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| (Y_CONST(ybty1),_) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "gte" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "gte" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				end
			| (_,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "gte" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "gte" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				end
			| (_,_) ->
				begin
					if ((compare v1 v2) == 0) then
						begin
							if (mode == 0) then
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
    				 		Y_VAR(newval),
    						Y_NAMED_TYPED("event"),
    				 		[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 		[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
    						 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
    				  	[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
							else
								(lhsclk,
    				 		lhsvalue,
    						Y_NAMED_TYPED("event"),
    				 		[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 		[Y_IMPLY(lhsclk,lhsvalue);
    						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
    				  	nv1@nv2)
						end
					else
						begin
							if (mode == 0) then
    						(* use uninterpreted function *)
    						let (newclk,newval) = create_uninterpreted_vars expr "gte" v1 v2 in
    						(Y_VAR(newclk),
    				 	 	Y_VAR(newval),
    						Y_BOOL,
    				 	 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 	 	vc1@vc2,
    				 	 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
							else
								let (newclk,newval) = create_uninterpreted_vars expr "gte" v1 v2 in
    						(lhsclk,
      				 	lhsvalue,
      					Y_BOOL,
      				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
      				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
    						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
      				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						end	
					end
			end
	
(** --------------------------------------------------------------------- *)

(** S_LT to yices *)
let lt_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue = 
	if ((is_event_type vt1) && (is_event_type vt2)) then
		begin
			if (mode == 0) then
				let (newclk,newval) = create_fresh_vars expr in
				(Y_VAR(newclk),
				Y_VAR(newval),
				Y_BOOL,
				[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
				[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
				[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
			else 
				(lhsclk,
				lhsvalue,
				Y_BOOL,
				[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
				 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
				nv1@nv2)
		end
	else if ((is_event_type vt1) && not (is_event_type vt2)) then
		begin
			match vt2 with
			| Y_CONST(ybtype) ->
				begin
					match v2 with
					| (Y_CFALSE | Y_CTRUE) -> 
						begin
							if (mode == 0) then
  							let (newclk,newval) = create_fresh_vars expr in
  							(Y_VAR(newclk),
  				 			Y_VAR(newval),
  							Y_BOOL,
  				 			[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
  						   Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				  		[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
							else
								(lhsclk,
				 				lhsvalue,
								Y_BOOL,
				 				[Y_EQ(lhsclk,c1)]@cc1@cc2,
				 				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
						     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
				  			nv1@nv2)
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| Y_BOOL -> 
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_LT(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
		 				lhsvalue,
						Y_BOOL,
		 				[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
		 				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_LT(v1,v2)));
				     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
		  			nv1@nv2)
				end
			| _ -> raise (InvalidExprssion (expr_to_string expr))
		end
	else if (not (is_event_type vt1) && (is_event_type vt2)) then
		begin
			match vt1 with
			| Y_CONST(ybtype) ->
				begin
					match v1 with
					| Y_CTRUE -> 
						begin
							if (mode == 0) then
  							let (newclk,newval) = create_fresh_vars expr in
  							(Y_VAR(newclk),
  				 			Y_VAR(newval),
  							Y_BOOL,
  				 			[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 			[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
  						   Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				  		[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
							else
  							(lhsclk,
  				 			lhsvalue,
  							Y_BOOL,
  				 			[Y_EQ(lhsclk,c2)]@cc1@cc2,
  				 			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
  						   Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				  		nv1@nv2)
						end
					| Y_CFALSE ->
						begin
							if (mode == 0) then
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
    				 		Y_VAR(newval),
    						Y_NAMED_TYPED("event"),
    				 		[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 		[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
    						 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
    				  	[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
							else
								(lhsclk,
    				 		lhsvalue,
    						Y_NAMED_TYPED("event"),
    				 		[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 		[Y_IMPLY(lhsclk,lhsvalue);
    						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
    				  	nv1@nv2)
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| Y_BOOL -> 
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_LT(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_LT(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| _ -> raise (InvalidExprssion (expr_to_string expr))
		end
	else
		begin
			match (vt1,vt2) with
			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
				begin
					match (v1,v2) with
					| (Y_CFALSE,Y_CTRUE) -> 
						if (mode == 0) then
							(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
						else
							(lhsclk,
    				 	lhsvalue,
    					Y_NAMED_TYPED("event"),
    				 	cc1@cc2,
    				 	[Y_IMPLY(lhsclk,lhsvalue);
    					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
    				 	nv1@nv2)
					| ((Y_CTRUE,Y_CTRUE) | (Y_CTRUE,Y_CFALSE) | (Y_CFALSE,Y_CFALSE)) -> 
						if (mode == 0) then
							(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
						else
							(lhsclk,
    				 	lhsvalue,
    					Y_BOOL,
    				 	cc1@cc2,
    				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
    					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    				 	nv1@nv2)
					| (Y_VAR(const1),Y_VAR(const2)) ->
						begin
							let const_expr1 = Hashtbls.get_val_const_hashtbl const1 and
									const_expr2 = Hashtbls.get_val_const_hashtbl const2 in
							match (const_expr1,const_expr2) with
							| (Y_CNAT(nat1),Y_CNAT(nat2)) ->
								if ((compare (int_of_string nat1) (int_of_string nat2)) < 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							| (Y_CNAT(nat1),Y_CINT(i2)) ->
								if ((compare (int_of_string nat1) (int_of_string i2)) < 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							| (Y_CINT(i1),Y_CNAT(nat2)) ->
								if ((compare (int_of_string i1) (int_of_string nat2)) < 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							| (Y_CINT(i1),Y_CINT(i2)) ->
								if ((compare (int_of_string i1) (int_of_string i2)) < 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							
							| (Y_CREAL(r1),Y_CREAL(r2)) ->
								if ((compare (float_of_string r1) (float_of_string r2)) < 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							
							| (Y_CCHAR(c1),Y_CCHAR(c2)) ->
								let char1 = String.get c1 0 and
								    char2 = String.get c2 0 in
								if ((compare char1 char2) < 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							
							| (Y_CSTRING(str1),Y_CSTRING(str2)) ->
								begin
									match ybty1 with
									| Y_NAMED_TYPED(strtype) ->
										begin
      								if ((compare str1 str2) < 0) then
      									begin
      										if (mode == 0) then
      											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
      										else
      											(lhsclk,
                  				 	lhsvalue,
                  					Y_NAMED_TYPED("event"),
                  				 	cc1@cc2,
                  				 	[Y_IMPLY(lhsclk,lhsvalue);
                  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
                  				 	nv1@nv2)
      									end
      								else
      									begin
      										if (mode == 0) then
      											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
      										else
      											(lhsclk,
                  				 	lhsvalue,
                  					Y_BOOL,
                  				 	cc1@cc2,
                  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
                  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
                  				 	nv1@nv2)
      									end
										end
									| _ -> (Y_NOTHING,Y_NOTHING,Y_NOTYPE,[],[],[])
								end
							| _ -> raise (InvalidExprssion (expr_to_string expr))
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| (Y_CONST(ybty1),Y_BOOL) ->
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_LT(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_LT(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| (Y_BOOL,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_LT(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_LT(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| (Y_BOOL,Y_BOOL) ->
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_LT(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_LT(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| (Y_CONST(ybty1),_) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "lt" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "lt" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				end
			| (_,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "lt" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "lt" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				end
			| (_,_) ->
				begin
					if ((compare v1 v2) == 0) then
						begin
							if (mode == 0) then
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
    				 		Y_VAR(newval),
    						Y_BOOL,
    				 		[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 		[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
    						 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    				  	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
							else
								(lhsclk,
    				 		lhsvalue,
    						Y_BOOL,
    				 		[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 		[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
    						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    				  	nv1@nv2)
						end
					else
						begin
							if (mode == 0) then
    						(* use uninterpreted function *)
    						let (newclk,newval) = create_uninterpreted_vars expr "lt" v1 v2 in
    						(Y_VAR(newclk),
    				 	 	Y_VAR(newval),
    						Y_BOOL,
    				 	 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 	 	vc1@vc2,
    				 	 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
							else
								let (newclk,newval) = create_uninterpreted_vars expr "lt" v1 v2 in
    						(lhsclk,
      				 	lhsvalue,
      					Y_BOOL,
      				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
      				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
    						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
      				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						end	
					end
			end
	
(** --------------------------------------------------------------------- *)

(** S_LTE to yices *)
let lte_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue = 
	if ((is_event_type vt1) && (is_event_type vt2)) then
		begin
			if (mode == 0) then
				let (newclk,newval) = create_fresh_vars expr in
				(Y_VAR(newclk),
				Y_VAR(newval),
				Y_NAMED_TYPED("event"),
				[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
				 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
			else 
				(lhsclk,
				lhsvalue,
				Y_NAMED_TYPED("event"),
				[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
				[Y_IMPLY(lhsclk,lhsvalue);
				 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				nv1@nv2)
		end
	else if ((is_event_type vt1) && not (is_event_type vt2)) then
		begin
			match vt2 with
			| Y_CONST(ybtype) ->
				begin
					match v2 with
					| Y_CTRUE -> 
						begin
							if (mode == 0) then
								let (newclk,newval) = create_fresh_vars expr in
								(Y_VAR(newclk),
				 				Y_VAR(newval),
								Y_NAMED_TYPED("event"),
				 				[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
				 				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
						     Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				  			[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
							else
								(lhsclk,
				 				lhsvalue,
								Y_NAMED_TYPED("event"),
				 				[Y_EQ(lhsclk,c1)]@cc1@cc2,
				 				[Y_IMPLY(lhsclk,lhsvalue);
						     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				  			nv1@nv2)
						end
					| Y_CFALSE ->
						if (mode == 0) then
							let (newclk,newval) = create_fresh_vars expr in
    					(Y_VAR(newclk),
    				 	Y_VAR(newval),
    					Y_BOOL,
    				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
    				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_CFALSE));
    					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						else
							(lhsclk,
			 				lhsvalue,
							Y_BOOL,
			 				[Y_EQ(lhsclk,c2)]@cc1@cc2,
			 				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
					     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
			  			nv1@nv2)
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| Y_BOOL -> 
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_LTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(vt2)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
		 				lhsvalue,
						Y_BOOL,
		 				[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
		 				[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_LTE(v1,v2)));
				     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
		  			nv1@nv2)
				end
			| _ -> raise (InvalidExprssion (expr_to_string expr))
		end
	else if (not (is_event_type vt1) && (is_event_type vt2)) then
		begin
			match vt1 with
			| Y_CONST(ybtype) ->
				begin
					match v1 with
					| (Y_CFALSE | Y_CTRUE) -> 
						begin
							if (mode == 0) then
  							let (newclk,newval) = create_fresh_vars expr in
								(Y_VAR(newclk),
				 				Y_VAR(newval),
								Y_NAMED_TYPED("event"),
				 				[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
				 				[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
						     Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				  			[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
							else
  							(lhsclk,
				 				lhsvalue,
								Y_NAMED_TYPED("event"),
				 				[Y_EQ(lhsclk,c2)]@cc1@cc2,
				 				[Y_IMPLY(lhsclk,lhsvalue);
						     Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
				  			nv1@nv2)
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| Y_BOOL -> 
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_LTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_LTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| _ -> raise (InvalidExprssion (expr_to_string expr))
		end
	else
		begin
			match (vt1,vt2) with
			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
				begin
					match (v1,v2) with
					| ((Y_CFALSE,Y_CTRUE) | (Y_CFALSE,Y_CFALSE) | (Y_CTRUE,Y_CTRUE)) -> 
						if (mode == 0) then
							(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
						else
							(lhsclk,
    				 	lhsvalue,
    					Y_NAMED_TYPED("event"),
    				 	cc1@cc2,
    				 	[Y_IMPLY(lhsclk,lhsvalue);
    					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
    				 	nv1@nv2)
					| (Y_CTRUE,Y_CFALSE) -> 
						if (mode == 0) then
							(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
						else
							(lhsclk,
    				 	lhsvalue,
    					Y_BOOL,
    				 	cc1@cc2,
    				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
    					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
    				 	nv1@nv2)
					| (Y_VAR(const1),Y_VAR(const2)) ->
						begin
							let const_expr1 = Hashtbls.get_val_const_hashtbl const1 and
									const_expr2 = Hashtbls.get_val_const_hashtbl const2 in
							match (const_expr1,const_expr2) with
							| (Y_CNAT(nat1),Y_CNAT(nat2)) ->
								if ((compare (int_of_string nat1) (int_of_string nat2)) <= 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							| (Y_CNAT(nat1),Y_CINT(i2)) ->
								if ((compare (int_of_string nat1) (int_of_string i2)) <= 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							| (Y_CINT(i1),Y_CNAT(nat2)) ->
								if ((compare (int_of_string i1) (int_of_string nat2)) <= 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							| (Y_CINT(i1),Y_CINT(i2)) ->
								if ((compare (int_of_string i1) (int_of_string i2)) <= 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							
							| (Y_CREAL(r1),Y_CREAL(r2)) ->
								if ((compare (float_of_string r1) (float_of_string r2)) <= 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							
							| (Y_CCHAR(c1),Y_CCHAR(c2)) ->
								let char1 = String.get c1 0 and
								    char2 = String.get c2 0 in
								if ((compare char1 char2) <= 0) then
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_NAMED_TYPED("event"),
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,lhsvalue);
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
            				 	nv1@nv2)
									end
								else
									begin
										if (mode == 0) then
											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
										else
											(lhsclk,
            				 	lhsvalue,
            					Y_BOOL,
            				 	cc1@cc2,
            				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
            					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
            				 	nv1@nv2)
									end
							
							| (Y_CSTRING(str1),Y_CSTRING(str2)) ->
								begin
									match ybty1 with
									| Y_NAMED_TYPED(strtype) ->
										begin
      								if ((compare str1 str2) <= 0) then
      									begin
      										if (mode == 0) then
      											(Y_NOTHING,Y_CTRUE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
      										else
      											(lhsclk,
                  				 	lhsvalue,
                  					Y_NAMED_TYPED("event"),
                  				 	cc1@cc2,
                  				 	[Y_IMPLY(lhsclk,lhsvalue);
                  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
                  				 	nv1@nv2)
      									end
      								else
      									begin
      										if (mode == 0) then
      											(Y_NOTHING,Y_CFALSE,Y_CONST(Y_BOOL),cc1@cc2,vc1@vc2,nv1@nv2)
      										else
      											(lhsclk,
                  				 	lhsvalue,
                  					Y_BOOL,
                  				 	cc1@cc2,
                  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_CFALSE));
                  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
                  				 	nv1@nv2)
      									end
										end
									| _ -> (Y_NOTHING,Y_NOTHING,Y_NOTYPE,[],[],[])
								end
							| _ -> raise (InvalidExprssion (expr_to_string expr))
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| (Y_CONST(ybty1),Y_BOOL) ->
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_LTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_LTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| (Y_BOOL,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_LTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_LTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| (Y_BOOL,Y_BOOL) ->
				begin
					if (mode == 0) then
  					let (newclk,newval) = create_fresh_vars expr in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(Y_VAR(newclk),Y_EQ(Y_VAR(newval),Y_LTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_LTE(v1,v2)));
  					 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	nv1@nv2)
				end
			| (Y_CONST(ybty1),_) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "lte" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "lte" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				end
			| (_,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "lte" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					Y_BOOL,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "lte" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					Y_BOOL,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
				end
			| (_,_) ->
				begin
					if ((compare v1 v2) == 0) then
						begin
							if (mode == 0) then
    						let (newclk,newval) = create_fresh_vars expr in
    						(Y_VAR(newclk),
    				 		Y_VAR(newval),
    						Y_NAMED_TYPED("event"),
    				 		[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 		[Y_IMPLY(Y_VAR(newclk),Y_VAR(newval));
    						 Y_IMPLY(Y_NOT(Y_VAR(newclk)),Y_EQ(Y_VAR(newval),Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
    				  	[(newclk,Y_BOOL);(newval,Y_NAMED_TYPED("event"))]@nv1@nv2)
							else
								(lhsclk,
    				 		lhsvalue,
    						Y_NAMED_TYPED("event"),
    				 		[Y_EQ(lhsclk,c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 		[Y_IMPLY(lhsclk,lhsvalue);
    						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_NAMED_TYPED("event"))))]@vc1@vc2,
    				  	nv1@nv2)
						end
					else
						begin
							if (mode == 0) then
    						(* use uninterpreted function *)
    						let (newclk,newval) = create_uninterpreted_vars expr "lte" v1 v2 in
    						(Y_VAR(newclk),
    				 	 	Y_VAR(newval),
    						Y_BOOL,
    				 	 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
    				 	 	vc1@vc2,
    				 	 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
							else
								let (newclk,newval) = create_uninterpreted_vars expr "lte" v1 v2 in
    						(lhsclk,
      				 	lhsvalue,
      					Y_BOOL,
      				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
      				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
    						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_BOOL)))]@vc1@vc2,
      				 	[(newclk,Y_BOOL);(newval,Y_BOOL)]@nv1@nv2)
						end	
					end
			end
	
(** --------------------------------------------------------------------- *)

(** S_PLUS to yices *)
let plus_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue = 
	if (((is_event_type vt1) && (is_event_type vt2)) || 
	    ((is_event_type vt1) && not (is_event_type vt2)) ||
			(not (is_event_type vt1) && (is_event_type vt2))) then
		raise (InvalidExprssion (expr_to_string expr))
	else
		begin
			match (vt1,vt2) with
			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
				begin
					match (v1,v2) with
					| ((Y_CTRUE,_) | (Y_CFALSE,_) | (_,Y_CTRUE) | (_,Y_CFALSE)) -> 
						raise (InvalidExprssion (expr_to_string expr))
					| (Y_VAR(const1),Y_VAR(const2)) ->
						begin
							let const_expr1 = Hashtbls.get_val_const_hashtbl const1 and
									const_expr2 = Hashtbls.get_val_const_hashtbl const2 in
							match (const_expr1,const_expr2) with
							| (Y_CNAT(nat1),Y_CNAT(nat2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string nat1) + (int_of_string nat2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CNAT(nat1),Y_CINT(i2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string nat1) + (int_of_string i2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CINT(i1),Y_CNAT(nat2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string i1) + (int_of_string nat2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CINT(i1),Y_CINT(i2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string i1) + (int_of_string i2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CREAL(r1),Y_CREAL(r2)) ->
								begin
									let cstvalueplus = string_of_float ((float_of_string r1) +. (float_of_string r2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CREAL(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_REAL,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CREAL(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_REAL))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_REAL,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_REAL))]@nv1@nv2)
										end
								end
							| (Y_CCOMPLEX(cr1,ci1),Y_CCOMPLEX(cr2,ci2)) ->
								begin
									let r_cstvalueplus = string_of_float ((float_of_string cr1) +. (float_of_string cr2)) in
									let i_cstvalueplus = string_of_float ((float_of_string ci1) +. (float_of_string ci2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CCOMPLEX(r_cstvalueplus,i_cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_COMPLEX,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CCOMPLEX(r_cstvalueplus,i_cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_COMPLEX))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_COMPLEX,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_COMPLEX))]@nv1@nv2)
										end
								end
							| ((Y_CCHAR(_),_) | (_,Y_CCHAR(_)) | (Y_CSTRING(_),_) | (_,Y_CSTRING(_))) ->
								raise (InvalidExprssion (expr_to_string expr))
							| _ -> 
								raise (InvalidExprssion (expr_to_string expr))
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| (Y_CONST(ybty1),Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_CONST(ybty2)) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_CONST(ybty1),_) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "plus" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt2,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "plus" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt2,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
				end
			| (_,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "plus" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt1,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "plus" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end
			| (_,_) ->
				begin
					if (mode == 0) then
						(* use uninterpreted function *)
						let (newclk,newval) = create_uninterpreted_vars expr "plus" v1 v2 in
						(Y_VAR(newclk),
				 	 	Y_VAR(newval),
						vt1,
				 	 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
				 	 	vc1@vc2,
				 	 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "plus" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end	
			end
	
(** --------------------------------------------------------------------- *)

(** S_MINUS to yices *)
let minus_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue = 
	if (((is_event_type vt1) && (is_event_type vt2)) || 
	    ((is_event_type vt1) && not (is_event_type vt2)) ||
			(not (is_event_type vt1) && (is_event_type vt2))) then
		raise (InvalidExprssion (expr_to_string expr))
	else
		begin
			match (vt1,vt2) with
			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
				begin
					match (v1,v2) with
					| ((Y_CTRUE,_) | (Y_CFALSE,_) | (_,Y_CTRUE) | (_,Y_CFALSE)) -> 
						raise (InvalidExprssion (expr_to_string expr))
					| (Y_VAR(const1),Y_VAR(const2)) ->
						begin
							let const_expr1 = Hashtbls.get_val_const_hashtbl const1 and
									const_expr2 = Hashtbls.get_val_const_hashtbl const2 in
							match (const_expr1,const_expr2) with
							| (Y_CNAT(nat1),Y_CNAT(nat2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string nat1) - (int_of_string nat2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CNAT(nat1),Y_CINT(i2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string nat1) - (int_of_string i2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CINT(i1),Y_CNAT(nat2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string i1) - (int_of_string nat2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CINT(i1),Y_CINT(i2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string i1) - (int_of_string i2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CREAL(r1),Y_CREAL(r2)) ->
								begin
									let cstvalueplus = string_of_float ((float_of_string r1) -. (float_of_string r2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CREAL(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_REAL,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CREAL(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_REAL))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_REAL,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_REAL))]@nv1@nv2)
										end
								end
							| (Y_CCOMPLEX(cr1,ci1),Y_CCOMPLEX(cr2,ci2)) ->
								begin
									let r_cstvalueplus = string_of_float ((float_of_string cr1) -. (float_of_string cr2)) in
									let i_cstvalueplus = string_of_float ((float_of_string ci1) -. (float_of_string ci2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CCOMPLEX(r_cstvalueplus,i_cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_COMPLEX,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CCOMPLEX(r_cstvalueplus,i_cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_COMPLEX))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_COMPLEX,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_COMPLEX))]@nv1@nv2)
										end
								end
							| ((Y_CCHAR(_),_) | (_,Y_CCHAR(_)) | (Y_CSTRING(_),_) | (_,Y_CSTRING(_))) ->
								raise (InvalidExprssion (expr_to_string expr))
							| _ -> 
								raise (InvalidExprssion (expr_to_string expr))
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| (Y_CONST(ybty1),Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_CONST(ybty2)) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_CONST(ybty1),_) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "minus" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt2,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "minus" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt2,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
				end
			| (_,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "minus" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt1,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "minus" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end
			| (_,_) ->
				begin
					if (mode == 0) then
						(* use uninterpreted function *)
						let (newclk,newval) = create_uninterpreted_vars expr "minus" v1 v2 in
						(Y_VAR(newclk),
				 	 	Y_VAR(newval),
						vt1,
				 	 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
				 	 	vc1@vc2,
				 	 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "minus" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end	
			end
	
(** --------------------------------------------------------------------- *)

(** S_MULT to yices *)
let mult_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue = 
	if (((is_event_type vt1) && (is_event_type vt2)) || 
	    ((is_event_type vt1) && not (is_event_type vt2)) ||
			(not (is_event_type vt1) && (is_event_type vt2))) then
		raise (InvalidExprssion (expr_to_string expr))
	else
		begin
			match (vt1,vt2) with
			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
				begin
					match (v1,v2) with
					| ((Y_CTRUE,_) | (Y_CFALSE,_) | (_,Y_CTRUE) | (_,Y_CFALSE)) -> 
						raise (InvalidExprssion (expr_to_string expr))
					| (Y_VAR(const1),Y_VAR(const2)) ->
						begin
							let const_expr1 = Hashtbls.get_val_const_hashtbl const1 and
									const_expr2 = Hashtbls.get_val_const_hashtbl const2 in
							match (const_expr1,const_expr2) with
							| (Y_CNAT(nat1),Y_CNAT(nat2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string nat1) * (int_of_string nat2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CNAT(nat1),Y_CINT(i2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string nat1) * (int_of_string i2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CINT(i1),Y_CNAT(nat2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string i1) * (int_of_string nat2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CINT(i1),Y_CINT(i2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string i1) * (int_of_string i2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CREAL(r1),Y_CREAL(r2)) ->
								begin
									let cstvalueplus = string_of_float ((float_of_string r1) *. (float_of_string r2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CREAL(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_REAL,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CREAL(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_REAL))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_REAL,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_REAL))]@nv1@nv2)
										end
								end
							| (Y_CCOMPLEX(cr1,ci1),Y_CCOMPLEX(cr2,ci2)) ->
								begin
									let r_cstvalueplus = string_of_float ((float_of_string cr1) *. (float_of_string cr2) -. (float_of_string ci1) *. (float_of_string ci2)) in
									let i_cstvalueplus = string_of_float ((float_of_string ci1) *. (float_of_string cr2) +. (float_of_string cr1) *. (float_of_string ci2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CCOMPLEX(r_cstvalueplus,i_cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_COMPLEX,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CCOMPLEX(r_cstvalueplus,i_cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_COMPLEX))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_COMPLEX,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_COMPLEX))]@nv1@nv2)
										end
								end
							| ((Y_CCHAR(_),_) | (_,Y_CCHAR(_)) | (Y_CSTRING(_),_) | (_,Y_CSTRING(_))) ->
								raise (InvalidExprssion (expr_to_string expr))
							| _ -> 
								raise (InvalidExprssion (expr_to_string expr))
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| (Y_CONST(ybty1),Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_CONST(ybty2)) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_CONST(ybty1),_) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "mult" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt2,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "mult" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt2,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
				end
			| (_,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "mult" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt1,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "mult" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end
			| (_,_) ->
				begin
					if (mode == 0) then
						(* use uninterpreted function *)
						let (newclk,newval) = create_uninterpreted_vars expr "mult" v1 v2 in
						(Y_VAR(newclk),
				 	 	Y_VAR(newval),
						vt1,
				 	 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
				 	 	vc1@vc2,
				 	 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "mult" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end	
			end
	
(** --------------------------------------------------------------------- *)

(** S_DIV to yices *)
let div_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue = 
	if (((is_event_type vt1) && (is_event_type vt2)) || 
	    ((is_event_type vt1) && not (is_event_type vt2)) ||
			(not (is_event_type vt1) && (is_event_type vt2))) then
		raise (InvalidExprssion (expr_to_string expr))
	else
		begin
			match (vt1,vt2) with
			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
				begin
					match (v1,v2) with
					| ((Y_CTRUE,_) | (Y_CFALSE,_) | (_,Y_CTRUE) | (_,Y_CFALSE)) -> 
						raise (InvalidExprssion (expr_to_string expr))
					| (Y_VAR(const1),Y_VAR(const2)) ->
						begin
							let const_expr1 = Hashtbls.get_val_const_hashtbl const1 and
									const_expr2 = Hashtbls.get_val_const_hashtbl const2 in
							match (const_expr1,const_expr2) with
							| (Y_CNAT(nat1),Y_CNAT(nat2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string nat1) / (int_of_string nat2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CNAT(nat1),Y_CINT(i2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string nat1) / (int_of_string i2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CINT(i1),Y_CNAT(nat2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string i1) / (int_of_string nat2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CINT(i1),Y_CINT(i2)) ->
								begin
									let cstvalueplus = string_of_int ((int_of_string i1) / (int_of_string i2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_INT,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
										end
								end
							| (Y_CREAL(r1),Y_CREAL(r2)) ->
								begin
									let cstvalueplus = string_of_float ((float_of_string r1) /. (float_of_string r2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CREAL(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_REAL,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CREAL(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_REAL))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_REAL,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_REAL))]@nv1@nv2)
										end
								end
							| (Y_CCOMPLEX(cr1,ci1),Y_CCOMPLEX(cr2,ci2)) ->
								begin
									let cr1_value = (float_of_string cr1) and
											ci1_value = (float_of_string ci1) and
											cr2_value = (float_of_string cr2) and
											ci2_value = (float_of_string ci2) in
									let r_cstvalueplus = string_of_float ((cr1_value *. cr2_value +. ci1_value *. ci2_value) /. (cr2_value *. cr2_value +. ci2_value *. ci2_value)) in
									let i_cstvalueplus = string_of_float ((ci1_value *. cr2_value -. cr1_value *. ci2_value) /. (cr2_value *. cr2_value +. ci2_value *. ci2_value)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CCOMPLEX(r_cstvalueplus,i_cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_COMPLEX,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CCOMPLEX(r_cstvalueplus,i_cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_COMPLEX))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_COMPLEX,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_COMPLEX))]@nv1@nv2)
										end
								end
							| ((Y_CCHAR(_),_) | (_,Y_CCHAR(_)) | (Y_CSTRING(_),_) | (_,Y_CSTRING(_))) ->
								raise (InvalidExprssion (expr_to_string expr))
							| _ -> 
								raise (InvalidExprssion (expr_to_string expr))
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| (Y_CONST(ybty1),Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_CONST(ybty2)) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_CONST(ybty1),_) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "div" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt2,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "div" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt2,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
				end
			| (_,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "div" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt1,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "div" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end
			| (_,_) ->
				begin
					if (mode == 0) then
						(* use uninterpreted function *)
						let (newclk,newval) = create_uninterpreted_vars expr "div" v1 v2 in
						(Y_VAR(newclk),
				 	 	Y_VAR(newval),
						vt1,
				 	 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
				 	 	vc1@vc2,
				 	 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "div" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end	
			end
	
(** --------------------------------------------------------------------- *)

(** S_MODULO to yices *)
let modulo_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue = 
	if (((is_event_type vt1) && (is_event_type vt2)) || 
	    ((is_event_type vt1) && not (is_event_type vt2)) ||
			(not (is_event_type vt1) && (is_event_type vt2))) then
		raise (InvalidExprssion (expr_to_string expr))
	else
		begin
			match (vt1,vt2) with
			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
				begin
					match (v1,v2) with
					| ((Y_CTRUE,_) | (Y_CFALSE,_) | (_,Y_CTRUE) | (_,Y_CFALSE)) -> 
						raise (InvalidExprssion (expr_to_string expr))
					| (Y_VAR(const1),Y_VAR(const2)) ->
						begin
							let const_expr1 = Hashtbls.get_val_const_hashtbl const1 and
									const_expr2 = Hashtbls.get_val_const_hashtbl const2 in
							match (const_expr1,const_expr2) with
							| (Y_CNAT(nat1),Y_CNAT(nat2)) ->
								begin
									try
  									let cstvalueplus = string_of_int ((int_of_string nat1) mod (int_of_string nat2)) in
              			try
  										begin 
                				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
    										if (mode == 0) then
                					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
  											else
  												(lhsclk,
                    			lhsvalue,
                    			Y_INT,
                    			cc1@cc2,
                    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                           Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                    			nv1@nv2)
  										end
              			with SymNotFound(smsg) ->
  										begin
                				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
  											if (mode == 0) then
                					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
  											else
  												(lhsclk,
                    			lhsvalue,
                    			Y_INT,
                    			cc1@cc2,
                    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                           Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                    			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
  										end
									with Division_by_zero -> raise (InvalidExprssion (expr_to_string expr))
								end
							| (Y_CNAT(nat1),Y_CINT(i2)) ->
								begin
									try
  									let cstvalueplus = string_of_int ((int_of_string nat1) mod (int_of_string i2)) in
              			try
  										begin 
                				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
    										if (mode == 0) then
                					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
  											else
  												(lhsclk,
                    			lhsvalue,
                    			Y_INT,
                    			cc1@cc2,
                    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                           Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                    			nv1@nv2)
  										end
              			with SymNotFound(smsg) ->
  										begin
                				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
  											if (mode == 0) then
                					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
  											else
  												(lhsclk,
                    			lhsvalue,
                    			Y_INT,
                    			cc1@cc2,
                    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                           Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                    			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
  										end
									with Division_by_zero -> raise (InvalidExprssion (expr_to_string expr))
								end
							| (Y_CINT(i1),Y_CNAT(nat2)) ->
								begin
									try
  									let cstvalueplus = string_of_int ((int_of_string i1) mod (int_of_string nat2)) in
              			try
  										begin 
                				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
    										if (mode == 0) then
                					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
  											else
  												(lhsclk,
                    			lhsvalue,
                    			Y_INT,
                    			cc1@cc2,
                    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                           Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                    			nv1@nv2)
  										end
              			with SymNotFound(smsg) ->
  										begin
                				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
  											if (mode == 0) then
                					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
  											else
  												(lhsclk,
                    			lhsvalue,
                    			Y_INT,
                    			cc1@cc2,
                    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                           Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                    			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
  										end
									with Division_by_zero -> raise (InvalidExprssion (expr_to_string expr))
								end
							| (Y_CINT(i1),Y_CINT(i2)) ->
								begin
									try
  									let cstvalueplus = string_of_int ((int_of_string i1) mod (int_of_string i2)) in
              			try
  										begin 
                				let const_var = Hashtbls.get_const_hashtbl (Y_CINT(cstvalueplus)) in
    										if (mode == 0) then
                					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,nv1@nv2)
  											else
  												(lhsclk,
                    			lhsvalue,
                    			Y_INT,
                    			cc1@cc2,
                    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                           Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                    			nv1@nv2)
  										end
              			with SymNotFound(smsg) ->
  										begin
                				let const_var = create_const_vars (Y_CINT(cstvalueplus)) in
  											if (mode == 0) then
                					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_INT),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
  											else
  												(lhsclk,
                    			lhsvalue,
                    			Y_INT,
                    			cc1@cc2,
                    			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                           Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_INT)))]@vc1@vc2,
                    			[(const_var,Y_CONST(Y_INT))]@nv1@nv2)
  										end
									with Division_by_zero -> raise (InvalidExprssion (expr_to_string expr))
								end
							| ((Y_CCOMPLEX(_,_),Y_CCOMPLEX(_,_)) | (Y_CREAL(_),Y_CREAL(_)) | (Y_CCHAR(_),_) | (_,Y_CCHAR(_)) | (Y_CSTRING(_),_) | (_,Y_CSTRING(_))) ->
								raise (InvalidExprssion (expr_to_string expr))
							| _ -> 
								raise (InvalidExprssion (expr_to_string expr))
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| (Y_CONST(ybty1),Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_CONST(ybty2)) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_CONST(ybty1),_) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "mod" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt2,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "mod" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt2,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
				end
			| (_,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "mod" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt1,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "mod" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end
			| (_,_) ->
				begin
					if (mode == 0) then
						(* use uninterpreted function *)
						let (newclk,newval) = create_uninterpreted_vars expr "mod" v1 v2 in
						(Y_VAR(newclk),
				 	 	Y_VAR(newval),
						vt1,
				 	 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
				 	 	vc1@vc2,
				 	 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "mod" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end	
			end
	
(** --------------------------------------------------------------------- *)

(** S_POWER to yices *)
let power_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue = 
	if (((is_event_type vt1) && (is_event_type vt2)) || 
	    ((is_event_type vt1) && not (is_event_type vt2)) ||
			(not (is_event_type vt1) && (is_event_type vt2))) then
		raise (InvalidExprssion (expr_to_string expr))
	else
		begin
			match (vt1,vt2) with
			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
				begin
					match (v1,v2) with
					| ((Y_CTRUE,_) | (Y_CFALSE,_) | (_,Y_CTRUE) | (_,Y_CFALSE)) -> 
						raise (InvalidExprssion (expr_to_string expr))
					| (Y_VAR(const1),Y_VAR(const2)) ->
						begin
							let const_expr1 = Hashtbls.get_val_const_hashtbl const1 and
									const_expr2 = Hashtbls.get_val_const_hashtbl const2 in
							match (const_expr1,const_expr2) with
							| (Y_CNAT(nat1),Y_CNAT(nat2)) ->
								raise (InvalidExprssion (expr_to_string expr))
							| (Y_CNAT(nat1),Y_CINT(i2)) ->
								raise (InvalidExprssion (expr_to_string expr))
							| (Y_CINT(i1),Y_CNAT(nat2)) ->
								raise (InvalidExprssion (expr_to_string expr))
							| (Y_CINT(i1),Y_CINT(i2)) ->
								raise (InvalidExprssion (expr_to_string expr))
							| (Y_CREAL(r1),Y_CREAL(r2)) ->
								begin
									let cstvalueplus = string_of_float ((float_of_string r1) ** (float_of_string r2)) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CREAL(cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_REAL,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CREAL(cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_REAL),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_REAL))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_REAL,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_REAL)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_REAL))]@nv1@nv2)
										end
								end
							| (Y_CCOMPLEX(cr1,ci1),Y_CCOMPLEX(cr2,ci2)) ->
								raise (InvalidExprssion (expr_to_string expr))
							| ((Y_CCHAR(_),_) | (_,Y_CCHAR(_)) | (Y_CSTRING(_),_) | (_,Y_CSTRING(_))) ->
								raise (InvalidExprssion (expr_to_string expr))
							| _ -> 
								raise (InvalidExprssion (expr_to_string expr))
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| (Y_CONST(ybty1),Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_CONST(ybty2)) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_CONST(ybty1),_) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "power" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt2,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "power" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt2,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
				end
			| (_,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "power" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt1,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "power" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end
			| (_,_) ->
				begin
					if (mode == 0) then
						(* use uninterpreted function *)
						let (newclk,newval) = create_uninterpreted_vars expr "power" v1 v2 in
						(Y_VAR(newclk),
				 	 	Y_VAR(newval),
						vt1,
				 	 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
				 	 	vc1@vc2,
				 	 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "power" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end	
			end
	
(** --------------------------------------------------------------------- *)

(** S_COMPLEXDENOTE to yices: return a complex value *)
let complexdenote_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 mode lhsclk lhsvalue = 
	if (((is_event_type vt1) && (is_event_type vt2)) || 
	    ((is_event_type vt1) && not (is_event_type vt2)) ||
			(not (is_event_type vt1) && (is_event_type vt2))) then
		raise (InvalidExprssion (expr_to_string expr))
	else
		begin
			match (vt1,vt2) with
			| (Y_CONST(ybty1),Y_CONST(ybty2)) ->
				begin
					match (v1,v2) with
					| ((Y_CTRUE,_) | (Y_CFALSE,_) | (_,Y_CTRUE) | (_,Y_CFALSE)) -> 
						raise (InvalidExprssion (expr_to_string expr))
					| (Y_VAR(const1),Y_VAR(const2)) ->
						begin
							let const_expr1 = Hashtbls.get_val_const_hashtbl const1 and
									const_expr2 = Hashtbls.get_val_const_hashtbl const2 in
							match (const_expr1,const_expr2) with
							| (Y_CNAT(nat1),Y_CNAT(nat2)) ->
								raise (InvalidExprssion (expr_to_string expr))
							| (Y_CNAT(nat1),Y_CINT(i2)) ->
								raise (InvalidExprssion (expr_to_string expr))
							| (Y_CINT(i1),Y_CNAT(nat2)) ->
								raise (InvalidExprssion (expr_to_string expr))
							| (Y_CINT(i1),Y_CINT(i2)) ->
								raise (InvalidExprssion (expr_to_string expr))
							| (Y_CREAL(r1),Y_CREAL(r2)) ->
								begin
									let r_cstvalueplus = string_of_float (float_of_string r1) in
									let i_cstvalueplus = string_of_float (float_of_string r2) in
            			try
										begin 
              				let const_var = Hashtbls.get_const_hashtbl (Y_CCOMPLEX(r_cstvalueplus,i_cstvalueplus)) in
  										if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),cc1@cc2,vc1@vc2,nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_COMPLEX,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))]@vc1@vc2,
                  			nv1@nv2)
										end
            			with SymNotFound(smsg) ->
										begin
              				let const_var = create_const_vars (Y_CCOMPLEX(r_cstvalueplus,i_cstvalueplus)) in
											if (mode == 0) then
              					(Y_NOTHING,Y_VAR(const_var),Y_CONST(Y_COMPLEX),cc1@cc2,vc1@vc2,[(const_var,Y_CONST(Y_COMPLEX))]@nv1@nv2)
											else
												(lhsclk,
                  			lhsvalue,
                  			Y_COMPLEX,
                  			cc1@cc2,
                  			[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(const_var)));
                         Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(Y_COMPLEX)))]@vc1@vc2,
                  			[(const_var,Y_CONST(Y_COMPLEX))]@nv1@nv2)
										end
								end
							| (Y_CCOMPLEX(cr1,ci1),Y_CCOMPLEX(cr2,ci2)) ->
								raise (InvalidExprssion (expr_to_string expr))
							| ((Y_CCHAR(_),_) | (_,Y_CCHAR(_)) | (Y_CSTRING(_),_) | (_,Y_CSTRING(_))) ->
								raise (InvalidExprssion (expr_to_string expr))
							| _ -> 
								raise (InvalidExprssion (expr_to_string expr))
						end
					| _ -> raise (InvalidExprssion (expr_to_string expr))
				end
			| (Y_CONST(ybty1),Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_CONST(ybty2)) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_BOOL,Y_BOOL) ->
				raise (InvalidExprssion (expr_to_string expr))
			| (Y_CONST(ybty1),_) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "complexdenote" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt2,
  				 	[Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "complexdenote" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt2,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt2)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt2)]@nv1@nv2)
				end
			| (_,Y_CONST(ybty2)) ->
				begin
					if (mode == 0) then
  					(* use uninterpreted function *)
  					let (newclk,newval) = create_uninterpreted_vars expr "complexdenote" v1 v2 in
  					(Y_VAR(newclk),
  				 	Y_VAR(newval),
  					vt1,
  				 	[Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "complexdenote" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end
			| (_,_) ->
				begin
					if (mode == 0) then
						(* use uninterpreted function *)
						let (newclk,newval) = create_uninterpreted_vars expr "complexdenote" v1 v2 in
						(Y_VAR(newclk),
				 	 	Y_VAR(newval),
						vt1,
				 	 	[Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
				 	 	vc1@vc2,
				 	 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
					else
						let (newclk,newval) = create_uninterpreted_vars expr "complexdenote" v1 v2 in
						(lhsclk,
  				 	lhsvalue,
  					vt1,
  				 	[Y_EQ(lhsclk,Y_VAR(newclk));Y_EQ(Y_VAR(newclk),c1);Y_EQ(c1,c2)]@cc1@cc2,
  				 	[Y_IMPLY(lhsclk,Y_EQ(lhsvalue,Y_VAR(newval)));
						 Y_IMPLY(Y_NOT(lhsclk),Y_EQ(lhsvalue,Y_ABSENCE(vt1)))]@vc1@vc2,
  				 	[(newclk,Y_BOOL);(newval,vt1)]@nv1@nv2)
				end	
			end
	
(** --------------------------------------------------------------------- *)

(** translate an expression to: clock formula * value formula * list of constraint formulas * list of new local variables *)
let rec expr_to_yciesformula filetype paras inputs outputs locals typedefs expr =
	let (clk,value,value_type,clkc,valuec,nvl) = 
	match expr with
	|	S_NOTHING -> (Y_NOTHING,Y_NOTHING,Y_NOTYPE,[],[],[])
	
	|	S_CLKZERO -> (Y_CFALSE,Y_NOTHING,Y_NOTYPE,[],[],[])
	
	| S_CLKHAT(e) ->
		let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
		clkhat_expr_to_ycies expr c v vt cc vc nv 0 Y_NOTHING Y_NOTHING
		
	| S_CLKWHEN(b) ->
		let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs b in
		clkwhen_expr_to_ycies expr c v vt cc vc nv 0 Y_NOTHING Y_NOTHING		
			
	| S_CLKPLUS(e1,e2) ->
		let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and 
		(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in 
		clkplus_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
		
	| S_CLKMINUS(e1,e2) ->
		let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and
		(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in
		clkminus_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
		
	| S_CLKMULT(e1,e2) ->
		let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and 
		(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in
		clkmult_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
	
	(* constants *)
	| S_CONSTANT(c) ->
		constant_expr_to_ycies expr c 0 Y_NOTHING Y_NOTHING
		
	(* enumerator, array, struct, bundle *)
	| S_ENUMITEM(s,e) ->
		let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
		enumitem_expr_to_ycies s e typedefs c v vt cc vc nv 0 Y_NOTHING Y_NOTHING

	| S_ARRAYITEM(s,e) -> (Y_NOTHING,Y_NOTHING,Y_NOTYPE,[],[],[])
		
	| S_STRUCTITEM(e,s) -> (Y_NOTHING,Y_NOTHING,Y_NOTYPE,[],[],[])
		
	(* varable *)
	| S_VAR(s) ->
		begin
			try
				let (res,(varclass,vartype,(varname,initvalue))) = find_var_in_decs (paras@inputs@outputs@locals) s in
				match vartype with
				| T_CONST(bty) ->
					begin
						match varclass with
						| VAR_PARAMETER ->
							begin
								match filetype with
								| SRC_FILE -> 
									(Y_NOTHING,Y_VAR("v_"^s),Y_CONST((sig_abs_to_yices_abs_types vartype typedefs)),[],[],[])
								| CMP_FILE ->
									(Y_NOTHING,Y_VAR("v_"^s^"_c"),Y_CONST((sig_abs_to_yices_abs_types vartype typedefs)),[],[],[])
							end
						| _ ->
							let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs initvalue in
							(Y_NOTHING,v,vt,cc,vc,nv)
					end
				| _ -> 
					begin
						match filetype with
						| SRC_FILE -> 
							(Y_VAR("h_" ^ s),Y_VAR("v_" ^ s),(sig_abs_to_yices_abs_types vartype typedefs),[],[],[])
						| CMP_FILE ->
							(Y_VAR("h_" ^ s ^ "_c"),Y_VAR("v_" ^ s ^ "_c"),(sig_abs_to_yices_abs_types vartype typedefs),[],[],[])
					end
			with VariableNotFound(varmsg) -> raise (InvalidExprssion ((expr_to_string expr) ^ ": " ^ varmsg ^ " not found"))
		end
		
	(* conversions *)
	| S_CAST(ty,e) ->
		let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
		cast_expr_to_ycies expr c v vt cc vc nv ty typedefs 0 Y_NOTHING Y_NOTHING
		
	(* dynamic *)
	| S_DELAY(e) ->
		let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
		delay_expr_to_ycies expr c v vt cc vc nv 0 Y_NOTHING Y_NOTHING
		
	| S_DELAYINIT(e,ie) ->
		let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e and
				(ci,vi,vti,cci,vci,nvi) = expr_to_yciesformula filetype paras inputs outputs locals typedefs ie in
		delayinit_expr_to_ycies expr c v vt cc vc nv ci vi vti cci vci nvi 0 Y_NOTHING Y_NOTHING
		
	| S_DELAYBY(e,e1) ->
		let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
		delayby_expr_to_ycies expr c v vt cc vc nv 0 Y_NOTHING Y_NOTHING
		
	| S_DELAYBYINIT(e,e1,ie) ->
		let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e and
				(ci,vi,vti,cci,vci,nvi) = expr_to_yciesformula filetype paras inputs outputs locals typedefs ie in
		delaybyinit_expr_to_ycies expr c v vt cc vc nv ci vi vti cci vci nvi 0 Y_NOTHING Y_NOTHING
	
	(* temporal *)
	| S_DEFAULT(e1,e2) ->
		let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and
			  (c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in
		default_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
	
	| S_WHEN(e1,e2) ->
		let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and
				(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in
		when_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
	
	  (* unary op *)	
	| S_UNARY(uop,e) -> 
		begin
			match uop with
			| S_NOT ->
				let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
				not_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 0 Y_NOTHING Y_NOTHING
			| S_UPLUS -> 
				expr_to_yciesformula filetype paras inputs outputs locals typedefs e
			| S_UMINUS ->
				let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
				uminus_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 0 Y_NOTHING Y_NOTHING
		end
	
	(* boolean operations *)
	| S_BINARY(bop,e1,e2) ->
		begin
			let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and
					(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in
			match bop with
			| S_OR ->
				or_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
			| S_AND ->
				and_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
			| S_XOR ->
				xor_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
			| S_EQ ->
				eq_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
			| S_DIFF ->
				diff_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
			| S_GT ->
				gt_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
			| S_GTE ->
				gte_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING					
  		| S_LT ->
				lt_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING					
  		| S_LTE ->
				lte_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
			| S_PLUS ->
				plus_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
			| S_MINUS ->
				minus_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
			| S_MULT ->
				mult_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
			| S_DIV ->
				div_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
			| S_MODULO ->
				modulo_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
			| S_POWER ->
				power_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING
			| S_COPLEXDENOTE ->
				complexdenote_expr_to_ycies expr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 0 Y_NOTHING Y_NOTHING								
		end
		
		(* if then else *)
	| S_IF(e1,e2,e3) ->
		(Y_NOTHING,Y_NOTHING,Y_NOTYPE,[],[],[])
			
		(* (expr) *)
	| S_PCLOSE(e) ->
		expr_to_yciesformula filetype paras inputs outputs locals typedefs e
			
		(* tuple of expression *)
	| S_TUPLES(elst) ->
		(Y_NOTHING,Y_NOTHING,Y_NOTYPE,[],[],[])
	
		(* process call *)
	| S_PROCESSCALL(pn,paraexpres,ipexprs,rstexprs) ->
		(* get the equation list *)
		(* iter the list *)
		
		(Y_NOTHING,Y_NOTHING,Y_NOTYPE,[],[],[])
	
	| _ -> (Y_NOTHING,Y_NOTHING,Y_NOTYPE,[],[],[])
	
	in (clk,value,value_type,clkc,valuec,nvl)

(** --------------------------------------------------------------------- *)

(** S_CLKEQ to yices *)
let clkeq_to_yices eqlst filetype paras inputs outputs locals typedefs =
	try 
  	let (resc,rc,rcc,rvc,rnv) = (ref [],ref [],ref [],ref [],ref []) in
  	for i = 0 to ((List.length eqlst) - 1) do
  		begin
  			let (ci,vi,vti,cci,vci,nvi) = expr_to_yciesformula filetype paras inputs outputs locals typedefs (List.nth eqlst i) in
  			match ci with
  			| Y_NOTHING -> 
  				begin
  					rcc := !rcc @ cci;
  					rvc := !rvc @ vci;
  					rnv := !rnv @ nvi
  				end
  			| _ -> 
  				begin
  					rc := !rc @ [ci];
  					rcc := !rcc @ cci;
  					rvc := !rvc @ vci;
  					rnv := !rnv @ nvi
  				end
  		end
  	done;
		
  	for i = 0 to ((List.length !rc) - 2) do
  		resc := !resc @ [Y_EQ((List.nth !rc i),(List.nth !rc (i+1)))]
  	done;	
  	
  	if ((List.length !resc) > 1) then (Y_AND(!resc),Y_NOTHING,Y_NOTYPE,!rcc,!rvc,!rnv)
  	else ((List.hd !resc),Y_NOTHING,Y_NOTYPE,!rcc,!rvc,!rnv)
  
  with Failure(failuremsg) -> (Y_NOTHING,Y_NOTHING,Y_NOTYPE,[],[],[])

(** --------------------------------------------------------------------- *)

(** S_CLKLTE to yices *)
let clklte_to_yices filetype paras inputs outputs locals typedefs e1 e2 =
	let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and 
			(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in
	clkmult_expr_to_ycies (S_CLKMULT(e1,e2)) c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 c1 v1
	
(** --------------------------------------------------------------------- *)

(** SIGDEF(Y_VAR,Expr) to yices *)
let var_expr_to_yciesformula filetype paras inputs outputs locals typedefs lhsvar rhsexpr = 
	match rhsexpr with
		(* nothing *)
		|	S_NOTHING -> 
			(Y_NOTHING,[])
		(* clock operators *)
		|	S_CLKZERO -> 
			(Y_EQ(Y_VAR("h_"^lhsvar),Y_CFALSE),[])

		| S_CLKHAT(e) ->
			let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
			let (c1,v1,vt1,cc1,vc1,nv1) = clkhat_expr_to_ycies rhsexpr c v vt cc vc nv 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
			((and_yices_exprl_list (cc1@vc1)),nv1)
		
		| S_CLKWHEN(e) ->
			let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
			let (c1,v1,vt1,cc1,vc1,nv1) = clkwhen_expr_to_ycies rhsexpr c v vt cc vc nv 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
			((and_yices_exprl_list (cc1@vc1)),nv1)
		
		| S_CLKPLUS(e1,e2) ->
  		let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and 
  		(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in 
  		let (c3,v3,vt3,cc3,vc3,nv3) = clkplus_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
			((and_yices_exprl_list (cc3@vc3)),nv3)
		
		| S_CLKMINUS(e1,e2) ->
  		let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and
  		(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in
  		let (c3,v3,vt3,cc3,vc3,nv3) = clkminus_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
  		((and_yices_exprl_list (cc3@vc3)),nv3)
		
		| S_CLKMULT(e1,e2) ->
  		let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and 
  		(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in
  		let (c3,v3,vt3,cc3,vc3,nv3) = clkmult_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
			((and_yices_exprl_list (cc3@vc3)),nv3)
		
		(* constants *)
		| S_CONSTANT(c) ->
			let (c1,v1,vt1,cc1,vc1,nv1) = constant_expr_to_ycies rhsexpr c 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
			((and_yices_exprl_list (cc1@vc1)),nv1)
		
		| S_ENUMITEM(s,e) ->
			let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
			let (c1,v2,vt1,cc1,vc1,nv1) = enumitem_expr_to_ycies s e typedefs c v vt cc vc nv 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
			((and_yices_exprl_list (cc1@vc1)),nv1)
		
		| S_ARRAYITEM(s,e) -> (Y_NOTHING,[])
		
		| S_STRUCTITEM(e,s) -> (Y_NOTHING,[])
		
		(* varable *)
		| S_VAR(s) ->
  		begin
  			try
  				let (res,(varclass,vartype,(varname,initvalue))) = find_var_in_decs (paras @ inputs @ outputs @ locals) s in
  				match vartype with
  				| T_CONST(bty) ->
						begin
							match varclass with
							| VAR_PARAMETER ->
      					(and_yices_exprl_list ([Y_IMPLY(Y_VAR("h_"^lhsvar),Y_EQ(Y_VAR("v_"^lhsvar),Y_VAR("v_"^s)));
                Y_IMPLY(Y_NOT(Y_VAR("h_"^lhsvar)),Y_EQ(Y_VAR("v_"^lhsvar),Y_ABSENCE((sig_abs_to_yices_abs_types vartype typedefs))))]),
    						[])
							| _ ->
								let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs initvalue in
      					((and_yices_exprl_list (cc@
    						[Y_IMPLY(Y_VAR("h_"^lhsvar),Y_EQ(Y_VAR("v_"^lhsvar),v));
                Y_IMPLY(Y_NOT(Y_VAR("h_"^lhsvar)),Y_EQ(Y_VAR("v_"^lhsvar),Y_ABSENCE(vt)))]@vc)),
    						nv)
						end
  				| _ ->
						(and_yices_exprl_list ([Y_EQ(Y_VAR("h_"^lhsvar),Y_VAR("h_"^s));
						Y_IMPLY(Y_VAR("h_"^lhsvar),Y_EQ(Y_VAR("v_"^lhsvar),Y_VAR("v_"^s)));
            Y_IMPLY(Y_NOT(Y_VAR("h_"^lhsvar)),Y_EQ(Y_VAR("v_"^lhsvar),Y_ABSENCE((sig_abs_to_yices_abs_types vartype typedefs))))]),
						[])
  			with VariableNotFound(varmsg) -> raise (InvalidExprssion ((expr_to_string rhsexpr) ^ ": " ^ varmsg ^ " not found"))
  		end
		
		(* conversions *)
		| S_CAST(ty,e) ->
  		begin
  			let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
  			match ty with
  			| T_EVENT ->
					((and_yices_exprl_list ([Y_EQ(Y_VAR("h_"^lhsvar),c);
																	Y_IMPLY(Y_VAR("h_"^lhsvar),Y_VAR("v_"^lhsvar));
																	Y_IMPLY(Y_NOT(Y_VAR("h_"^lhsvar)),Y_EQ(Y_VAR("v_"^lhsvar),Y_ABSENCE(Y_BOOL)))]@cc@vc)),
					nv)
  			| T_NAMED_TYPED(namedtype) ->
  				begin
  					try
  						let basetype = get_basetype_typedef typedefs ty in
  						match basetype with
  						| T_EVENT -> 
								((and_yices_exprl_list ([Y_EQ(Y_VAR("h_"^lhsvar),c);
																	      Y_IMPLY(Y_VAR("h_"^lhsvar),Y_VAR("v_"^lhsvar));
																				Y_IMPLY(Y_NOT(Y_VAR("h_"^lhsvar)),Y_EQ(Y_VAR("v_"^lhsvar),Y_ABSENCE(Y_BOOL)))]@cc@vc)),
								nv)
  						| _ -> 
								((and_yices_exprl_list ([Y_EQ(Y_VAR("h_"^lhsvar),c);
																	 			Y_IMPLY(Y_VAR("h_"^lhsvar),Y_EQ(Y_VAR("v_"^lhsvar),v));
																				Y_IMPLY(Y_NOT(Y_VAR("h_"^lhsvar)),Y_EQ(Y_VAR("v_"^lhsvar),Y_ABSENCE((sig_abs_to_yices_abs_types ty typedefs))))]@cc@vc)),
								nv)
  					with TypedefNotFound(msg) -> 
							((and_yices_exprl_list ([Y_EQ(Y_VAR("h_"^lhsvar),c);
																	 		Y_IMPLY(Y_VAR("h_"^lhsvar),Y_EQ(Y_VAR("v_"^lhsvar),v));
																			Y_IMPLY(Y_NOT(Y_VAR("h_"^lhsvar)),Y_EQ(Y_VAR("v_"^lhsvar),Y_ABSENCE((sig_abs_to_yices_abs_types ty typedefs))))]@cc@vc)),
							nv)
  				end
  			| _ ->
					((and_yices_exprl_list ([Y_EQ(Y_VAR("h_"^lhsvar),c);
																	 			Y_IMPLY(Y_VAR("h_"^lhsvar),Y_EQ(Y_VAR("v_"^lhsvar),v));
																				Y_IMPLY(Y_NOT(Y_VAR("h_"^lhsvar)),Y_EQ(Y_VAR("v_"^lhsvar),Y_ABSENCE((sig_abs_to_yices_abs_types ty typedefs))))]@cc@vc)),
					nv)
  		end
		
		(* dynamic *)
		| S_DELAY(e) ->
			let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
			let (c1,v1,vt1,cc1,vc1,nv1) = delay_expr_to_ycies rhsexpr c v vt cc vc nv 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
			((and_yices_exprl_list (cc1@vc1)),nv1)
		
		| S_DELAYINIT(e,ie) ->
			let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e and
					(ci,vi,vti,cci,vci,nvi) = expr_to_yciesformula filetype paras inputs outputs locals typedefs ie in
			let (c1,v1,vt1,cc1,vc1,nv1) = delayinit_expr_to_ycies rhsexpr c v vt cc vc nv ci vi vti cci vci nvi 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
			((and_yices_exprl_list (cc1@vc1)),nv1)
		
		| S_DELAYBY(e,e1) ->
			let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
			let (c1,v1,vt1,cc1,vc1,nv1) = delayby_expr_to_ycies rhsexpr c v vt cc vc nv 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
			((and_yices_exprl_list (cc1@vc1)),nv1)
		
		| S_DELAYBYINIT(e,e1,ie) ->
			let (c,v,vt,cc,vc,nv) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e and
					(ci,vi,vti,cci,vci,nvi) = expr_to_yciesformula filetype paras inputs outputs locals typedefs ie in
			let (c1,v1,vt1,cc1,vc1,nv1) = delaybyinit_expr_to_ycies rhsexpr c v vt cc vc nv ci vi vti cci vci nvi 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
			((and_yices_exprl_list (cc1@vc1)),nv1)
		
		(* temporal *)
		| S_DEFAULT(e1,e2) ->
			let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and
			  	(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in
			let (c3,v3,vt3,cc3,vc3,nv3) = default_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
			((and_yices_exprl_list (cc3@vc3)),nv3)
	
		| S_WHEN(e1,e2) ->
			let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and
					(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in
			let (c3,v3,vt3,cc3,vc3,nv3) = when_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
			((and_yices_exprl_list (cc3@vc3)),nv3)
	
		  (* unary op *)	
		| S_UNARY(uop,e) -> 
  		begin
  			match uop with
  			| S_NOT ->
  				let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
  				let (c2,v2,vt2,cc2,vc2,nv2) = not_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc2@vc2)),nv2)
  			| S_UPLUS -> 
  				let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
					((and_yices_exprl_list ([Y_EQ(Y_VAR("h_"^lhsvar),c1);
																	 			Y_IMPLY(Y_VAR("h_"^lhsvar),Y_EQ(Y_VAR("v_"^lhsvar),v1));
																				Y_IMPLY(Y_NOT(Y_VAR("h_"^lhsvar)),Y_EQ(Y_VAR("v_"^lhsvar),Y_ABSENCE(vt1)))]@cc1@vc1)),
					nv1)
  			| S_UMINUS ->
  				let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
  				let (c2,v2,vt2,cc2,vc2,nv2) = uminus_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc2@vc2)),nv2)
  		end
		
			(* boolean operations *)
		| S_BINARY(bop,e1,e2) ->
  		begin
  			let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 in
  			let	(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in
  			match bop with
  			| S_OR ->
  				let (c3,v3,vt3,cc3,vc3,nv3) = or_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
  			| S_AND ->
  				let (c3,v3,vt3,cc3,vc3,nv3) = and_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
  			| S_XOR ->
  				let (c3,v3,vt3,cc3,vc3,nv3) = xor_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
  			| S_EQ ->
  				let (c3,v3,vt3,cc3,vc3,nv3) = eq_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
  			| S_DIFF ->
  				let (c3,v3,vt3,cc3,vc3,nv3) = diff_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
  			| S_GT ->
  				let (c3,v3,vt3,cc3,vc3,nv3) = gt_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
				| S_GTE ->
					let (c3,v3,vt3,cc3,vc3,nv3) = gte_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
  			| S_LT ->
					let (c3,v3,vt3,cc3,vc3,nv3) = lt_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
  			| S_LTE ->
					let (c3,v3,vt3,cc3,vc3,nv3) = lte_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
				| S_PLUS ->
					let (c3,v3,vt3,cc3,vc3,nv3) = plus_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
				| S_MINUS ->
					let (c3,v3,vt3,cc3,vc3,nv3) = minus_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
				| S_MULT ->
					let (c3,v3,vt3,cc3,vc3,nv3) = mult_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
				| S_DIV ->
					let (c3,v3,vt3,cc3,vc3,nv3) = div_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
				| S_MODULO ->
					let (c3,v3,vt3,cc3,vc3,nv3) = modulo_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
				| S_POWER ->
					let (c3,v3,vt3,cc3,vc3,nv3) = power_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
				| S_COPLEXDENOTE ->
					let (c3,v3,vt3,cc3,vc3,nv3) = complexdenote_expr_to_ycies rhsexpr c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 (Y_VAR("h_"^lhsvar)) (Y_VAR("v_"^lhsvar)) in
					((and_yices_exprl_list (cc3@vc3)),nv3)
  		end
			(* if then else *)
		| S_IF(e1,e2,e3) ->
			(Y_NOTHING,[])
			
			(* (expr) *)
		| S_PCLOSE(e) ->
			let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e in
			((and_yices_exprl_list ([Y_EQ(Y_VAR("h_"^lhsvar),c1);
															Y_IMPLY(Y_VAR("h_"^lhsvar),Y_EQ(Y_VAR("v_"^lhsvar),v1));
															Y_IMPLY(Y_NOT(Y_VAR("h_"^lhsvar)),Y_EQ(Y_VAR("v_"^lhsvar),Y_ABSENCE(vt1)))]@cc1@vc1)),
															nv1)
			(* tuple of expression *)
		| S_TUPLES(elst) ->
			(Y_NOTHING,[])
			
		| _ -> (Y_NOTHING,[])

(** --------------------------------------------------------------------- *)

(** translate a statement to ycies formula *)
let statement_to_yciesformula filetype procname paras inputs outputs locals typedefs stm =
	match stm with
		(* nothing *)
	| NOP -> (Y_NOTHING,[])
		(* clock constraints *)
	| CLKCONS(clkexpr) ->
		begin
			match clkexpr with
			| S_CLKEQ(eqlst) ->
				let (c,v,vt,cc,vc,nv) = clkeq_to_yices eqlst filetype paras inputs outputs locals typedefs in
				((and_yices_exprl_list ([c]@cc)),nv)
				
			| S_CLKLTE(e1,e2) ->
				let (c,v,vt,cc,vc,nv) = clklte_to_yices filetype paras inputs outputs locals typedefs e1 e2 in
				((and_yices_exprl_list cc),nv)
				
			| S_CLKGTE(e1,e2) ->
				let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and 
						(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in
				let (c,v,vt,cc,vc,nv) = clkplus_expr_to_ycies (S_CLKPLUS(e1,e2)) c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 c1 v1 in
				((and_yices_exprl_list cc),nv)
				
			| S_CLKDIFF(e1,e2) ->
				let (c1,v1,vt1,cc1,vc1,nv1) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e1 and 
						(c2,v2,vt2,cc2,vc2,nv2) = expr_to_yciesformula filetype paras inputs outputs locals typedefs e2 in
				let (c,v,vt,cc,vc,nv) = clkmult_expr_to_ycies (S_CLKMULT(e1,e2)) c1 v1 vt1 cc1 vc1 nv1 c2 v2 vt2 cc2 vc2 nv2 1 Y_CFALSE Y_NOTHING in
				((and_yices_exprl_list cc),nv)
				
			| _ -> raise (InvalidStatement (stm_to_string stm))
		end
		(* signal definition *)
	| SIGDEF(lhs,rhs) ->
		begin
			match lhs with
			| S_VAR(lhsvar) ->
				begin
					match filetype with
					| SRC_FILE ->
						let (f,nv) = var_expr_to_yciesformula filetype paras inputs outputs locals typedefs lhsvar rhs in
						Hashtbls.add_source_yices_formula_hashtbl 1 f;
						(f,nv)
					| CMP_FILE ->
						let (f,nv) = var_expr_to_yciesformula filetype paras inputs outputs locals typedefs (lhsvar ^ "_c") rhs in
						Hashtbls.add_source_yices_formula_hashtbl 1 f;
						(f,nv)
				end
			| S_PCLOSE(lhsexpr) ->
				begin
					match lhsexpr with
					| S_VAR(lhsvar) ->
						var_expr_to_yciesformula filetype paras inputs outputs locals typedefs lhsvar rhs
					| _ -> raise (InvalidStatement (stm_to_string stm))
				end
				(* tuple, process call with outputs*)
			| S_TUPLES(lhsvarlist) ->
				(Y_NOTHING,[])
				(* process call without outputs *)
			| S_NOTHING ->
				begin
					match rhs with
					| S_PROCESSCALL(pn,paraexprs,inputexprs,rstexprs) ->
						(Y_NOTHING,[])
					| _ -> raise (InvalidStatement (stm_to_string stm))
				end
			| _ -> raise (InvalidStatement (stm_to_string stm))
		end
