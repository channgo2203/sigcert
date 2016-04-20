(*
 * Description : Signal IR.
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>

 * This module construct an abstract syntax 
 * representation of a Signal origram
 *)

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
	| T_ENUM of string * string list 																				(** name and given item values *)
	| T_ARRAY of base_type * expression list 																(** type and sizes *)
	| T_STRUCT of string * single_name list 																(** name and given fields *)
	| T_BUNDLE of string * single_name list * expression
	| T_EXTERNAL of string
	| T_CONST of base_type 																									(** "constant" modifier *)
	| T_NAMED_TYPED of string 																							(** named type comming form "type" *)
	| T_PROCESS of string 																									(** process name for calling *)
	| T_TUPLES of base_type list 																						(** tuple type, e.g. (int,real,char) *)

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
		(** declaration of a variable: e.g. integer x, y, z *)
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
		(** clock constraints *)
	| CLKCONS of expression

(** expression *)
and expression =
		(** null expression, e.g. left hand side of a process call without outputs *)
		S_NOTHING
		(** clock expression *)
	|	S_CLKZERO
	| S_CLKHAT of expression 																					(** ^x : clock of signal x *)
	| S_CLKWHEN of expression 																				(** when b : [b] *)
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
	| S_DELAY of expression 																					(** x$ *)
	| S_DELAYINIT of expression * expression 													(** x$ init x0 *)
	| S_DELAYBY of expression * expression 														(** x$1 *)
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
	| S_COMPLEX of string * string (** real and image *)
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

(** Check a variable name in a dec *)
val find_var_in_dec : declaration -> string -> bool * single_name

(** Find a variable by name in dec list *)
val find_var_in_decs : declaration list -> string -> bool * single_name

(** Check a dec is constant dec *)
val is_const_var_in_dec : declaration -> bool

(** Get constant vars *)
val get_const_vars_in_decs : declaration list -> declaration list

(** Check var is a constant var *)
val is_const_var_in_decs : declaration list -> string -> bool

(** Find a typdef in a dec *)
val find_typedef_in_dec : declaration -> string -> bool * base_type * name

(** Find a typedef by name in decs *)
val find_typedef_in_decs : declaration list -> string -> bool * base_type * name

(** Find a enum by its item name *)
val find_enumdef_in_decs : declaration list -> string -> bool * base_type * name

(** Get var type in dec *)
val get_var_type_in_dec : declaration -> string -> base_type

(** Get var type in declaration list *)
val get_var_type_in_decs : declaration list -> string -> base_type

(** Get base type of a typedef *)
val get_basetype_typedef : declaration list -> base_type -> base_type

(** Size compare *)
val size_compare : size -> size -> bool

(** Sign compare *)
val sign_compare : sign -> sign -> bool

(** Type compare *)
val type_compare : base_type -> base_type -> bool

(** Get all input var names *)
val varname_from_decs : declaration list -> string list

(** Check a var is event *)
val is_event_type : declaration list -> string -> bool

(** Check a var is boolean *)
val is_bool_type : declaration list -> string -> bool

(** Varclass to string *)
val varclass_to_string : var_class -> string

(** Size to string *)
val size_to_string : size -> string

(** Sign to string *)
val sign_to_string : sign -> string

(** Base type to string *)
val type_to_string : base_type -> string

(** Display a declaration *)
val declaration_print : declaration -> out_channel -> unit

(** Display a declaration list *)
val declaration_list_print : declaration list -> out_channel -> unit

(** Expression to string *)
val expr_to_string : expression -> string

(** Statement to string *)
val stm_to_string : statement -> string

(** Display statement *)
val stm_print : statement -> out_channel -> unit

(** Display a statement list *)
val stm_list_print : statement list -> out_channel -> unit

(** Display a process *)
val process_def_print : process_def -> out_channel -> unit
