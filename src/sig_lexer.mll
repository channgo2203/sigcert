(*
 * Description : lexical analyzer of Signal
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 *)

{
open Sig_parser
open Exceptions
open Errors

(*
 * Positions
 *)
let update_handle_lineno () =
	let num = Input_handle.curlineno() in 
	Input_handle.set_lineno (num + 1)
 
let update_handle_line str = 
	Input_handle.set_line str

let update_handle_file name = 
	Input_handle.set_name name

let update_handle_pos pos =
	Input_handle.set_pos pos

(*
 * Keyword hashtable 
 *)
let create_hashtable size init =
	let tbl = Hashtbl.create size in
  List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
	tbl

let keyword_table =
	create_hashtable 100 [
  	("event", EVENT);
		("boolean", BOOL);
		("short", SHORT);
		("integer", INT);
		("long", LONG);
		("real", REAL);
		("complex", COMPLEX);
		("char", CHAR);
		("string",  STRING);
		("enum", ENUM);
		("struct", STRUCT);
		("bundle", BUNDLE);
		("process", PROCESS);
		("action", ACTION);
		("node", NODE);
		("function", FUNCTION);
		("safe", SAFE);
		("deterministic", DETERMINISTIC);
		("unsafe", UNSAFE);
		("spec", SPEC);
		("init", INIT);
		("true", TRUE);
		("false", FALSE);
		("constant", CONSTANT);
		("shared", SHARED);
		("statevar", STATEVAR);
		("pragmas", PRAGMAS);
		("end", END);
		("type", TYPE);
		("window", WINDOW);
		("default", DEFAULT);
		("when", WHEN);
		("cell", CELL);
		("not", NOT);
		("and", AND);
		("or", OR);
		("xor", XOR);
		("modulo", MODULO);
		("if", IF);
		("then", THEN);
		("else", ELSE);
		("where", WHERE);
		("external", EXTERNAL)
	]

(*
 * Useful primitives 
 *)
let scan_ident id =
	try
  	let token = Hashtbl.find keyword_table id in
    token
  with Not_found ->
    IDENTIFIER (id)

(*
 * Remove quotes 
 *)
let rem_quotes str = 
	String.sub str 1 ((String.length str) - 2)

let scan_escape str =
	match str with
	"n" -> "\n"
	| "r" -> "\r"
	| "t" -> "\t"
	| "b" -> "\b"
	| _ -> str

let get_value chr =
	match chr with
	'0'..'9' -> (Char.code chr) - (Char.code '0')
	| 'a'..'z' -> (Char.code chr) - (Char.code 'a') + 10
	| 'A'..'Z' -> (Char.code chr) - (Char.code 'A') + 10
	| _ -> 0

let scan_hex_escape str =
	String.make 1 (Char.chr (
		(get_value (String.get str 0)) * 16
		+ (get_value (String.get str 1))
	))

let scan_oct_escape str =
	String.make 1 (Char.chr (
		(get_value (String.get str 0)) * 64
		+ (get_value (String.get str 1)) * 8
		+ (get_value (String.get str 2))
	))
}

(* lexer's patterns *)
let	decdigit = ['0'-'9']
let octdigit = ['0'-'7']
let hexdigit = ['0'-'9' 'a'-'f' 'A'-'F']
let letter = ['a'- 'z' 'A'-'Z']

let mark = ['.' ''' '"' '%' ':' '=' '<' '>' '+' '-' '*' '/' '@' '$' '^' '#' '|']
let delimitor = ['(' ')' '{' '}' '[' ']' '?' '!' ',' ';']
let space = '\\' ['x' 'X'] '2' '0'
let long_separator = '\\' ['x' 'X'] ['9' 'a' 'A' 'c' 'C' 'd' 'D']

let escape = '\\' _
let hex_escape = '\\' ['x' 'X'] hexdigit hexdigit
let oct_escape = '\\' octdigit octdigit octdigit

let name_char = letter | decdigit | '_'

let intnum = decdigit+
let octnum = '0' ['o' 'O'] octdigit+
let hexnum = '0' ['x' 'X'] hexdigit+

let exponent = ['e' 'E'] ['+' '-']? decdigit+
let fraction  = '.' decdigit+
let floatraw = (intnum? fraction)
			|(intnum exponent)
			|(intnum? fraction exponent)
			|(intnum '.') 
let floatnum = (intnum fraction) | (intnum fraction exponent) | (intnum exponent)

let blank = [' ' '\t']
let ident = (letter|'_')(letter|decdigit|'_')*


rule token = parse
  | '%'			{ let _ = comment lexbuf in token lexbuf }
	| blank		{ token lexbuf }
	| '\n'		{ update_handle_lineno(); token lexbuf }
	| '('			{ LPAREN }
	| ')'			{ RPAREN }
	|	'['			{ LSQUAREPAREN }
	| ']'			{ RSQUAREPAREN }
	| ',' 		{ COMMA }
	| '='			{ EQ }
	| '>'			{ GT }
	| '<'			{	LT }
	|	'@'			{ COMPLEXDENOTE }
	| '+'			{ PLUS }
	| '-'			{ MINUS }
	| '*'			{ MULT }
	| '/'			{ DIV }
	| ';'			{ SEMICOLON }
	| '{'			{ LBRACE }
	| '}'			{ RBRACE }
	| '?'			{ QUESTIONMARK }
	| '!'			{	EXCMARK }
	| '#'			{ NUMBERSIGN }
	| '|'			{ VERTICALBAR }
	| '$'			{ DOLLAR }
	| '^'			{ HAT }
	| ":="		{ DOTEQ }
	| "^0"		{ CLKZERO }
	| "^+"		{	CLKPLUS }
	| "^-"		{ CLKMINUS }
	| "^*"		{ CLKMULT }
	| "^="		{ CLKEQ }
	| "^<"		{ CLKLTE }
	| "^>"		{ CLKGTE }
	| "^#"		{ CLKDIFF }
	| "/="		{ DIFF }
	| ">="		{ GTE }
	| "<="		{	LTE }
	| "**"		{	POWER }
	| "(|"		{ LPAVER }
	| "|)"		{ RPAVER }
	| intnum  
		{ 
			NUM_INT (Lexing.lexeme lexbuf) 
		}
	| hexnum  
		{ 
			NUM_INT (Lexing.lexeme lexbuf) 
		}
	| octnum 
		{ 
			NUM_INT (Lexing.lexeme lexbuf)
		}
	| floatnum 
		{ 
			NUM_FLOAT (Lexing.lexeme lexbuf) 
		}
	| '\'' 		{ CHARACTER_CONST ( chr lexbuf) }
	| '"' 		{ STRING_CONST (str lexbuf) }
	| ident
		{
			scan_ident (Lexing.lexeme lexbuf)
		} 
	| eof 
		{
			EOF
		}
	| _
		{
			update_handle_line (Lexing.lexeme lexbuf);
			update_handle_pos (Lexing.lexeme_start lexbuf);
			display_error
				(Input_handle.curfile())
				(Input_handle.curlineno())
				(Input_handle.curline())
				(Input_handle.curoutchannel())
				"Invalid symbol";
			token lexbuf
		}
		
and comment = parse 	
	'%'			{ () }
	| _			{	comment lexbuf }

and str = parse
	'"'						{ "" }
	| hex_escape 	{ let cur = scan_hex_escape (String.sub 
									(Lexing.lexeme lexbuf) 2 2) in cur ^ (str lexbuf) }
	| oct_escape 	{ let cur = scan_oct_escape (String.sub 
									(Lexing.lexeme lexbuf) 1 3) in cur ^ (str lexbuf) }
	| "\\0"				{ (String.make 1 (Char.chr 0)) ^ (str lexbuf) }
	| escape			{ let cur = scan_escape (String.sub 
									(Lexing.lexeme lexbuf) 1 1) in cur ^ (str lexbuf) }
	| _ 					{ let cur = Lexing.lexeme lexbuf in cur ^ (str lexbuf) }

and chr = parse
  '\''					{ "" }
	| hex_escape 	{ let cur = scan_hex_escape (String.sub 
									(Lexing.lexeme lexbuf) 2 2) in cur ^ (chr lexbuf) }
	| oct_escape 	{ let cur = scan_oct_escape (String.sub 
									(Lexing.lexeme lexbuf) 1 3) in cur ^ (chr lexbuf) }
	| "\\0"				{ (String.make 1 (Char.chr 0)) ^ (chr lexbuf) }
	| escape			{ let cur = scan_escape (String.sub 
									(Lexing.lexeme lexbuf) 1 1) in cur ^ (chr lexbuf) }
	| _ 					{ let cur = Lexing.lexeme lexbuf in cur ^ (chr lexbuf) }
{
	
}
