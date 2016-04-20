(*
 * Description : Signal IR.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>

 * This module construct an abstract syntax 
 * representation of a Signal program
 *)

open Exceptions

(** file type *)
type file_type =
	| SRC_FILE
	| CMP_FILE

(** Size of int *)
and size =
		NO_SIZE				(** no size modifier *)
	| SHORT					(** "short" modifier *)
	| LONG					(** "long" modifier *)

(** Signess of int and bitfields *)
and sign =
		NO_SIGN					(** no sign modifier *)
	| SIGNED 					(** "signed" modifier *)
	| UNSIGNED				(** "unsigned" modifier *)

(** the classification of a variable (input, output,...) *)
and var_class =
		NO_CLASS
	| VAR_PARAMETER
	| VAR_INPUT
	| VAR_OUTPUT
	| VAR_LOCAL
	| VAR_SHARED
	| VAR_STATE of int 			(** level of depth *)

and base_type =
		NO_TYPE
	|	T_EVENT
	| T_BOOL
	| T_INT of size * sign
	| T_REAL
	| T_COMPLEX
	| T_CHAR of sign
	| T_STRING
	| T_ENUM of string * string list 																					(** name and given item values *)
	| T_ARRAY of base_type * expression list 																	(** type and sizes *)
	| T_STRUCT of string * single_name list 																	(** name and given fields *)
	| T_BUNDLE of string * single_name list * expression
	| T_EXTERNAL of string
	| T_CONST of base_type 																										(** "constant" modifier *)
	| T_NAMED_TYPED of string 																								(** named type comming form "type" *)
	| T_PROCESS of string 																										(** process name for calling *)
	| T_TUPLES of base_type list 																							(** tuple type, e.g. (int,real,char) *)

(** a name in a declaration with identifier, full type, initialization expression *)
and name = string * expression

(** ex. integer a, b, c *)
and group_name = var_class * base_type * name list

(** a single name, with only one declaration *)
and single_name = var_class * base_type * name

(** declarations found in a Signal process *)
and declaration = 
		(** declaration of a "type" *)
		TYPEDEF of base_type * name
		(** declaration of a variable *)
	|	VARDEF of group_name

(** defintion of a process : 
 *  name, list of parameters, inputs, outputs, locals, and statements
 *)	
and process_def = {
		name : string;
		paramenters : declaration list;
		inputs : declaration list;
		outputs : declaration list;
		locals : declaration list;
		typedefs : declaration list;
		equations : statement list;
		hiddenprocs : hiddenprocess_def list;
		}

(** e.g. (| x := y when b | z := u default v |)/ y, u *)
and hiddenprocess_def = {
		hiddenlocals : name list;
		hiddenequations : statement list;
		}
		
(** defintion of signal, clock *)
and statement =
		(** no operation *)
	 	NOP			
		(** definotion of signal e.g. y := x when b *)	
	|	SIGDEF of expression * expression
		(** clock constraints: ^=, ^<, ^>, ^# *)
	| CLKCONS of expression

(** expression *)
and expression =
		(** null expression *)
		S_NOTHING
		(** clock expression *)
	|	S_CLKZERO
	| S_CLKHAT of expression (** ^x : clock of signal x *)
	| S_CLKWHEN of expression (** when b : [b] *)
	| S_CLKPLUS of expression * expression
	| S_CLKMINUS of expression * expression
	| S_CLKMULT of expression * expression
	| S_CLKEQ of expression list
	| S_CLKLTE of expression * expression
	| S_CLKGTE of expression * expression
	| S_CLKDIFF of expression * expression
		(** constants *)
	| S_CONSTANT of constant
		(** enumerator, array, struct, bundle *)
	| S_ENUMITEM of string * expression
	| S_ARRAYITEM of string * expression
	| S_STRUCTITEM of string * expression
		(** variable *)
	| S_VAR of string
		(** conversions *)
	| S_CAST of base_type * expression
		(** dynamic *)
	| S_DELAY of expression 																																(** x$ *)
	| S_DELAYINIT of expression * expression 																								(** x$ init x0 *)
	| S_DELAYBY of expression * expression 																									(** x$1 *)
	| S_DELAYBYINIT of expression * expression * expression
	| S_WINDOW of expression * expression
	| S_WINDOWINIT of expression * expression * expression
		(** temporal *)
	| S_DEFAULT of expression * expression
	| S_WHEN of expression * expression
	| S_CELL of expression * expression
	| S_CELLINIT of expression * expression * expression
		(** unary operations *)
	| S_UNARY of unary_operator * expression
		(** binary operations *)
	| S_BINARY of binary_operator * expression * expression
		(** if *)
	| S_IF of expression * expression * expression
		(** process call: process name, parameters, inputs, restrictions *)
	| S_PROCESSCALL of string * expression list * expression list * expression list
		(** parenthese close expression *)
	| S_PCLOSE of expression
		(** tuples: sequence of expressions *)
	| S_TUPLES of expression list

and constant = 
	  S_TRUE
	| S_FALSE
	|	S_INT of string
	| S_REAL of string
	| S_COMPLEX of string * string 																														(** real and image *)
	| S_CHAR of string
	| S_STRING of string

and unary_operator =
		S_NOT 								(** "not" *)
	| S_UPLUS								(** "+" *)
	| S_UMINUS							(** "-" *)

and binary_operator =
		S_OR									(** "or" *)
  | S_AND									(** "and" *)
  | S_XOR									(** "xor" *)
	| S_EQ									(** "=" *)
	| S_DIFF								(** "/=" *)
	| S_GT 									(** ">" *)
	| S_GTE 								(** ">=" *)
  | S_LT									(** "<" *)
  | S_LTE 								(** "<=" *)
	| S_PLUS 								(** "+" *)
	| S_MINUS 							(** "-" *)
	| S_MULT 								(** "*" *)
	| S_DIV 								(** "/" *)
	| S_MODULO 							(** "modulo" *)
	| S_POWER 							(** "**" *)
	| S_COPLEXDENOTE 				(** "@" *)

(** Signal file is a set of processes and process tree *)
and sig_file = process_def list * Ptree.t

(** Find a variable in a name list *)
let find_var_in_namelist nl str =
	try
		let name = List.find (fun (n,e) -> if ((compare n str) == 0) then true else false) nl in 
		(true,name)
	with Not_found -> 
		(false,("",S_NOTHING))

(** --------------------------------------------------------------------- *)

(** Find a variable in a declaration *)
let find_var_in_dec dec str =
	match dec with
	| VARDEF((vc,ty,nl)) -> 
		let (res,name) = find_var_in_namelist nl str in (res,(vc,ty,name))
	| _ -> (false,(NO_CLASS,NO_TYPE,("",S_NOTHING)))

(** --------------------------------------------------------------------- *)

(** Find a variable by name in dec list *)
let find_var_in_decs decs str = 
	try
		let isfound = List.find (fun dec -> 
												     let (res,sname) = find_var_in_dec dec str in
												     res) decs in
		find_var_in_dec isfound str
	with Not_found -> 
		raise (VariableNotFound str)

(** --------------------------------------------------------------------- *)
														
(** Find a variable by name *)
let find_var_by_name proc str = 
	find_var_in_decs (proc.paramenters @ proc.inputs @ proc.outputs @ proc.locals) str

(** --------------------------------------------------------------------- *)
	
(** Check a dec is constant dec *)
let is_const_var_in_dec dec =
	match dec with
	| VARDEF((cvar,cty,cnl)) -> 
		begin
			match cty with
			| T_CONST(_) -> true
			| _ -> false
		end
	| _ -> false

(** --------------------------------------------------------------------- *)
	
(** Get constant vars *)
let get_const_vars_in_decs decs =
	try
		List.find_all (is_const_var_in_dec) decs
	with Not_found -> []

(** --------------------------------------------------------------------- *)

(** Check var is a constant var *)
let is_const_var_in_decs decs str =
	let (res,_) = find_var_in_decs (get_const_vars_in_decs decs) str in
	res

(** --------------------------------------------------------------------- *)

(** Find a typedef in declaration *)
let find_typedef_in_dec dec str =
		match dec with
		| TYPEDEF(ty,(name,e)) -> 
			if ((compare name str) == 0) then (true,ty,(name,e)) 
			else (false,NO_TYPE,("",S_NOTHING))
		| _ -> (false,NO_TYPE,("",S_NOTHING))

(** --------------------------------------------------------------------- *)

(** Find a typedef by name in decs *)
let find_typedef_in_decs decs str = 
	try
		let isfound = List.find (fun dec -> 
												     let (res,_,_) = find_typedef_in_dec dec str in
												     res) decs in
		find_typedef_in_dec isfound str
	with Not_found -> 
		raise (TypedefNotFound str)

(** --------------------------------------------------------------------- *)

(** Find an enum in a dec by its element name *)
let find_enumdef_in_dec dec str =
	match dec with
	| TYPEDEF(ty,(name,e)) ->
		begin
			match ty with
			| T_ENUM(ename,elist) ->
				begin
					try
						let _ = List.find (fun elementname ->
											 if ((compare elementname str) == 0) then true else false) elist in
						true
					with Not_found -> false
				end
			| _ -> false
		end
	| _ -> false

(** --------------------------------------------------------------------- *)

(** Find an enum by its item name *)
let find_enumdef_in_decs decs str =
	try
		let enumfound = List.find (fun dec ->
															 find_enumdef_in_dec dec str) decs in
		match enumfound with
		| TYPEDEF(ty,name) -> (true,ty,name)
		| _ -> (false,NO_TYPE,("",S_NOTHING))
	with Not_found -> (false,NO_TYPE,("",S_NOTHING))

(** --------------------------------------------------------------------- *)

(** Get var type in dec *)
let get_var_type_in_dec dec str = 
	let (res,(vc,ty,name)) = find_var_in_dec dec str in
	ty
		
(** --------------------------------------------------------------------- *)
		 
(** Get var type in decs *)
let get_var_type_in_decs decs str = 
	let (res,(vc,ty,name)) = find_var_in_decs decs str in
	ty

(** --------------------------------------------------------------------- *)

(** Get base type of a typedef *)
let get_basetype_typedef typedecs namedtype =
	match namedtype with
	| T_NAMED_TYPED(n) ->
		let (res,ty,name) = find_typedef_in_decs typedecs n in ty
	| _ -> namedtype

(** --------------------------------------------------------------------- *)

(** Size compare *)
let size_compare s1 s2 =
	match (s1,s2) with
		((NO_SIZE,_) | (_,NO_SIZE) | (SHORT,SHORT) | (LONG,LONG)) -> true
	| (_,_) -> false

(** --------------------------------------------------------------------- *)

(** Sign compare *)
let sign_compare s1 s2 =
	match (s1,s2) with
		((NO_SIGN,_) | (_,NO_SIGN) | (SIGNED,SIGNED) | (UNSIGNED,UNSIGNED)) -> true
	| (_,_) -> false

(** --------------------------------------------------------------------- *)

(** Type compare *)
let rec type_compare type1 type2 =
	match (type1,type2) with
	| ((NO_TYPE,_) | (_,NO_TYPE)) -> true
	| (T_EVENT,T_EVENT) -> true
	| (T_BOOL,T_BOOL) -> true
	| (T_INT(sz1,s1),T_INT(sz2,s2)) -> (size_compare sz1 sz2) && (sign_compare s1 s2)
	| (T_REAL,T_REAL) -> true
	| (T_COMPLEX,T_COMPLEX) -> true
	| (T_CHAR(s1),T_CHAR(s2)) -> (sign_compare s1 s2)
	| (T_STRING,T_STRING) -> true
	| (T_ENUM(n1,il1),T_ENUM(n2,il2)) -> 
		if ((List.length il1) == (List.length il2)) then
				((compare n1 n2) == 0) && (List.fold_left2 (fun b str1 str2 -> b && ((compare str1 str2) == 0)) true il1 il2)
		else false
	| (T_ARRAY(ty1,exprsl1),T_ARRAY(ty2,exprsl2)) -> type_compare ty1 ty2
	| (T_STRUCT(n1,fl1),T_STRUCT(n2,fl2)) -> 
		if ((List.length fl1) == (List.length fl2)) then
			begin
				let res = ref true in
				for i = 0 to (List.length fl1) do
					let (vc1,ty1,(name1,_)) = List.nth fl1 i and (vc2,ty2,(name2,_)) = List.nth fl2 i in
					res := !res && ((compare name1 name2) == 0)
				done;
				!res && ((compare n1 n2) == 0)
			end
		else false
	| (T_BUNDLE(n1,fl1,e1),T_BUNDLE(n2,fl2,e2)) ->
		if ((List.length fl1) == (List.length fl2)) then
		begin
				let res = ref true in
				for i = 0 to (List.length fl1) do
					let (vc1,ty1,(name1,_)) = List.nth fl1 i and (vc2,ty2,(name2,_)) = List.nth fl2 i in
					res := !res && ((compare name1 name2) == 0)
				done;
				!res && ((compare n1 n2) == 0)
			end
		else false
	| (T_EXTERNAL(s1),T_EXTERNAL(s2)) -> ((compare s1 s2) == 0)
	| (T_CONST(ty1),_) -> type_compare ty1 type2
	| (_,T_CONST(ty2)) -> type_compare type1 ty2
	| (T_NAMED_TYPED(s1),T_NAMED_TYPED(s2)) -> ((compare s1 s2) == 0)
	| (T_PROCESS(s1),T_PROCESS(s2)) -> ((compare s1 s2) == 0)
	| (T_TUPLES(tyl1),T_TUPLES(tyl2)) -> 
		if ((List.length tyl1) == (List.length tyl2)) then
			List.fold_left2 (fun b ty1 ty2 -> b && (type_compare ty1 ty2)) true tyl1 tyl2
		else false
	| (_,_) -> false

(** --------------------------------------------------------------------- *)	

(** Get all input var names *)
let varname_from_decs decs =
	let nl = List.flatten (List.map (fun dec -> match dec with
	| VARDEF((vc,ty,nl)) -> nl
	| _ -> []) decs 
  ) in
	let (namel,_) = List.split nl in namel
	
(** --------------------------------------------------------------------- *)

(** Check a var is event *)
let is_event_type decs str =
	try
		let ty = get_var_type_in_decs decs str in
		(type_compare ty T_EVENT)
	with VariableNotFound(ect) -> false

(** --------------------------------------------------------------------- *)

(** Check a var is boolean *)
let is_bool_type decs str = 
	try
		let ty = get_var_type_in_decs decs str in
		(type_compare ty T_BOOL)
	with VariableNotFound(ect) -> false
	
(** --------------------------------------------------------------------- *)

(** Size to string *)
let size_to_string s = 
	match s with
		NO_SIZE -> "no size"		(** no size modifier *)
	| SHORT	-> "short"				(** "short" modifier *)
	| LONG -> "long"					(** "long" modifier *)

(** --------------------------------------------------------------------- *)

(** Sign to string *)
let sign_to_string sign = 
	match sign with
		NO_SIGN -> "no sign"					(** no sign modifier *)
	| SIGNED -> "signed" 						(** "signed" modifier *)
	| UNSIGNED -> "unsigned"				(** "unsigned" modifier *)

(** --------------------------------------------------------------------- *)

(** Varclass to string *)
let varclass_to_string varclass = 
	match varclass with
		NO_CLASS -> "no class"
	| VAR_PARAMETER -> "parameter"
	| VAR_INPUT -> "input"
	| VAR_OUTPUT -> "output"
	| VAR_LOCAL -> "local"
	| VAR_SHARED -> "shared"
	| VAR_STATE(i) -> "state -" ^ (string_of_int i)

(** --------------------------------------------------------------------- *)

(** string list to string *)
let stringlist_to_string strl = 
		let res = ref "" in
  	List.iter (fun str -> res := !res ^ str ^ ", ") strl;
		if ((String.length !res) > 2) then (String.sub !res 0 ((String.length !res) - 2))
		else ""
(** --------------------------------------------------------------------- *)

(** Base type to string *)
let rec type_to_string t =
	match t with
		NO_TYPE -> ""
	|	T_EVENT -> "event"
	| T_BOOL -> "bool"
	| T_INT(s,u) -> "integer"
	| T_REAL -> "real"
	| T_COMPLEX -> "complex"
	| T_CHAR(u) -> "char"
	| T_STRING -> "string"
	| T_ENUM(n,l) -> "enum {" ^ (stringlist_to_string l) ^ "}"
	| T_ARRAY(t,l) -> "[] " ^ (type_to_string t) 
	| T_STRUCT(_,_) -> "struct"
	| T_BUNDLE(_,_,_) -> "bundle"
	| T_EXTERNAL(s) -> s
	| T_CONST(t) -> "constant " ^ (type_to_string t)
	| T_NAMED_TYPED(t) -> t
	| T_PROCESS(p) -> "process: " ^ p
	| T_TUPLES(tyl) -> "tuples"

(** --------------------------------------------------------------------- *)

(** String to int *)
let string_to_int num = 
	try
		let i = int_of_string num in
		i
	with Failure "int_of_string" -> 0

(** String to float *)
let string_to_float num_float =
	try
		let nf = float_of_string num_float in
		nf
	with Failure "float_of_string" -> 0.0

(** --------------------------------------------------------------------- *)

(** constant to string *)
let constant_to_string cons =
	match cons with
	  S_TRUE -> "true"
	| S_FALSE -> "false"
	|	S_INT(i) -> string_of_int (string_to_int i)
	| S_REAL(r) -> string_of_float (string_to_float r)
	| S_COMPLEX(r,i) -> (string_of_float (string_to_float r)) ^ "@" ^ string_of_float (string_to_float i)
	| S_CHAR(c) -> "\'" ^ c ^ "\'" 
	| S_STRING(s) -> "\"" ^ s ^ "\""

(** --------------------------------------------------------------------- *)

(** unary operator to string *)
let unary_operator_to_string uop =
	match uop with
		S_NOT -> "not "							(** "not" *)
	| S_UPLUS	-> "+"							(** "+" *)
	| S_UMINUS -> "-"							(** "-" *)

(** --------------------------------------------------------------------- *)

(** binary operator to string *)
let binary_operator_string bop =
	match bop with
		S_OR -> "or"									(** "or" *)
  | S_AND -> "and"								(** "and" *)
  | S_XOR	-> "xor"								(** "xor" *)
	| S_EQ -> "="									  (** "=" *)
	| S_DIFF -> "/="								(** "/=" *)
	| S_GT -> ">" 									(** ">" *)
	| S_GTE -> ">=" 								(** ">=" *)
  | S_LT -> "<"										(** "<" *)
  | S_LTE -> "<=" 								(** "<=" *)
	| S_PLUS -> "+"									(** "+" *)
	| S_MINUS -> "-" 								(** "-" *)
	| S_MULT -> "*"									(** "*" *)
	| S_DIV -> "/" 									(** "/" *)
	| S_MODULO -> "modulo" 					(** "modulo" *)
	| S_POWER -> "**" 							(** "**" *)
	| S_COPLEXDENOTE -> "@" 				(** "@" *)

(** --------------------------------------------------------------------- *)

(** expression to string *)
let rec expr_to_string expr =
	match expr with
		(** null expression *)
		S_NOTHING -> ""
		(** clock expression *)
	|	S_CLKZERO -> "^0"
	| S_CLKHAT(e) -> "^" ^ (expr_to_string e)
	| S_CLKWHEN(e) -> "when " ^ (expr_to_string e)
	| S_CLKPLUS(e1,e2) -> (expr_to_string e1) ^ " ^+ " ^ (expr_to_string e2)
	| S_CLKMINUS(e1,e2) -> (expr_to_string e1) ^ " ^- " ^ (expr_to_string e2)
	| S_CLKMULT(e1,e2) -> (expr_to_string e1) ^ " ^* " ^ (expr_to_string e2)
	| S_CLKEQ(clkl) -> 
		let res = ref "" in
		List.iter (fun lckeq -> res := !res ^ (expr_to_string lckeq) ^ " ^= ") clkl;
		if ((String.length !res) >= 3) then (String.sub !res 0 ((String.length !res) - 3))
		else ""
	| S_CLKLTE(e1,e2) -> (expr_to_string e1) ^ " ^< " ^ (expr_to_string e2)
	| S_CLKGTE(e1,e2) -> (expr_to_string e1) ^ " ^> " ^ (expr_to_string e2)
	| S_CLKDIFF(e1,e2) -> (expr_to_string e1) ^ " ^# " ^ (expr_to_string e2)
		(** constants *)
	| S_CONSTANT(c) -> constant_to_string c
		(** enumerator, array, struct, bundle *)
	| S_ENUMITEM(e1,e2) -> e1 ^ "#" ^ (expr_to_string e2)
	| S_ARRAYITEM(e1,e2) -> e1 ^ "[" ^ (expr_to_string e2) ^"]"
	| S_STRUCTITEM(_,_) -> "struct"
		(** varable *)
	| S_VAR(var) -> var
		(** conversions *)
	| S_CAST(ty,e) -> (type_to_string ty) ^ "(" ^ (expr_to_string e) ^ ")"
		(** dynamic *)
	| S_DELAY(e) -> (expr_to_string e) ^"$"
	| S_DELAYINIT(e1,e2) -> (expr_to_string e1) ^ "$ init " ^ (expr_to_string e2)
	| S_DELAYBY(e1,e2) -> (expr_to_string e1) ^ "$" ^ (expr_to_string e2)
	| S_DELAYBYINIT(e1,e2,e3) -> (expr_to_string e1) ^ "$" ^ (expr_to_string e2) ^ " init " ^ (expr_to_string e3)
	| S_WINDOW(e1,e2) -> (expr_to_string e1) ^ " windows " ^ (expr_to_string e2)
	| S_WINDOWINIT(e1,e2,e3) -> (expr_to_string e1) ^ " windows " ^ (expr_to_string e2) ^ " init " ^ (expr_to_string e3)
		(** temporal *)
	| S_DEFAULT(e1,e2) -> (expr_to_string e1) ^ " default " ^ (expr_to_string e2)
	| S_WHEN(e1,e2) -> (expr_to_string e1) ^ " when " ^ (expr_to_string e2)
	| S_CELL(e1,e2) -> (expr_to_string e1) ^ " cell " ^ (expr_to_string e2)
	| S_CELLINIT(e1,e2,e3) -> (expr_to_string e1) ^ " cell " ^ (expr_to_string e2) ^ " init " ^ (expr_to_string e3)
		(** unary operations *)
	| S_UNARY(uop,e) -> (unary_operator_to_string uop) ^ (expr_to_string e)
		(** binary operations *)
	| S_BINARY(bop,e1,e2) -> (expr_to_string e1) ^ " " ^ (binary_operator_string bop) ^ " " ^ (expr_to_string e2)
		(** if *)
	| S_IF(e1,e2,e3) -> "if " ^ (expr_to_string e1) ^ " then " ^ (expr_to_string e2) ^ " else " ^ (expr_to_string e3)
		(** process call: process name, parameters, inputs, restrictions *)
	| S_PROCESSCALL(e1,parl,inl,resl) -> 
		let exprs_to_string exprs =
			let res = ref "" in
  		List.iter (fun expr -> res := !res ^ (expr_to_string expr) ^ ", ") exprs;
			if ((String.length !res) >= 2) then (String.sub !res 0 ((String.length !res) - 2))
			else ""	
			in
		(e1) ^ "{" ^ (exprs_to_string parl) ^ "}" ^ "(" ^ (exprs_to_string inl) ^ ")" ^ "/" ^ (exprs_to_string resl)
	| S_PCLOSE(e) -> "(" ^ expr_to_string e ^ ")"    
		(** tuples: sequence of expressions *)
	| S_TUPLES(exprs) -> 
		let exprs_to_string exprs =
			let res = ref "" in
  		List.iter (fun expr -> res := !res ^ (expr_to_string expr) ^ ", ") exprs;
			if ((String.length !res) >= 2) then (String.sub !res 0 ((String.length !res) - 2))
			else ""	
			in
		"(" ^ (exprs_to_string exprs) ^ ")"

(** --------------------------------------------------------------------- *)

(** Statement to string *)
let stm_to_string stm =
	match stm with
	 	NOP -> ""	
		(** definotion of signal e.g. y := x when b *)	
	|	SIGDEF(e1,e2) -> 
		begin 
			match e1 with 
			| S_NOTHING -> expr_to_string e2
			|_ -> (expr_to_string e1) ^ " := " ^ (expr_to_string e2)
		end
		(** clock constraints *)
	| CLKCONS(e) -> expr_to_string e

(** --------------------------------------------------------------------- *)

(** Name list to string *)
let namelist_to_string namel = 
		let res = ref "" in
		List.iter (fun (n,expr) -> 
			match expr with
			| S_NOTHING -> res := !res ^ n ^ ", "
			|_ -> res := !res ^ n ^ " init " ^ (expr_to_string expr) ^ ", ") namel;
		if ((String.length !res) > 2) then (String.sub !res 0 ((String.length !res) - 2))
		else ""

(** --------------------------------------------------------------------- *)
		
(** Display a declaration *)
let declaration_print dec oc =
	match dec with
	| TYPEDEF(t,n) -> let (name,expr) = n in Printf.fprintf oc "type %s = %s\n" name (type_to_string t)
	| VARDEF(gr) -> 
		let (vc,ty,nl) = gr in
		Printf.fprintf oc "[%s] %s %s\n" (varclass_to_string vc) (type_to_string ty) (namelist_to_string nl)

let declaration_list_print decl oc =
	List.iter (fun dec -> declaration_print dec oc) decl

(** Display statement *)
let stm_print stm oc = 
	match stm with
	 	NOP -> ()		
		(** definotion of signal e.g. y := x when b *)	
	|	SIGDEF(e1,e2) -> 
		begin 
			match e1 with 
			| S_NOTHING -> Printf.fprintf oc "%s\n" (expr_to_string e2)
			|_ -> Printf.fprintf oc "%s := %s\n" (expr_to_string e1) (expr_to_string e2)
		end
		(** clock constraints *)
	| CLKCONS(e) -> Printf.fprintf oc "%s\n" (expr_to_string e)

(** --------------------------------------------------------------------- *)	

(** Display a statement list *)
let stm_list_print stml oc =
	List.iter (fun stm -> stm_print stm oc) stml

(** --------------------------------------------------------------------- *)	

(** Display a process *)
let process_def_print proc oc =
	Printf.fprintf oc "Process\nName: %s\n" proc.name;
	Printf.fprintf oc "Parameters:\n";
	declaration_list_print proc.paramenters oc;
	Printf.fprintf oc "Inputs:\n";
	declaration_list_print proc.inputs oc;
	Printf.fprintf oc "Output:\n";
	declaration_list_print proc.outputs oc;
	Printf.fprintf oc "Locals:\n";
	declaration_list_print proc.locals oc;
	Printf.fprintf oc "Typedefs:\n";
	declaration_list_print proc.typedefs oc;
	Printf.fprintf oc "Equations:\n";
	stm_list_print proc.equations oc

(** --------------------------------------------------------------------- *)