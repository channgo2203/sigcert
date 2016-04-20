# 8 "src/sig_lexer.mll"
 
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

# 123 "src/sig_lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\207\255\208\255\078\000\210\255\211\255\156\000\180\000\
    \031\000\179\000\232\255\005\000\234\255\235\255\236\255\237\255\
    \238\255\239\255\035\000\094\000\242\255\243\255\244\255\076\000\
    \077\000\247\255\248\255\249\255\250\255\251\255\015\000\253\255\
    \254\255\255\255\217\255\220\255\219\255\218\255\221\255\216\255\
    \222\255\223\255\224\255\225\255\226\255\227\255\228\255\229\255\
    \230\255\221\000\253\000\234\000\007\001\030\001\244\000\064\001\
    \091\001\101\001\118\001\128\001\138\001\103\000\254\255\255\255\
    \229\000\250\255\148\001\255\255\251\255\156\001\164\001\189\001\
    \227\001\254\255\172\001\253\255\162\000\250\255\212\001\255\255\
    \251\255\253\001\005\002\029\002\052\002\254\255\084\002\253\255\
    ";
  Lexing.lex_backtrk = 
   "\255\255\255\255\255\255\046\000\255\255\255\255\040\000\040\000\
    \048\000\024\000\255\255\022\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\015\000\014\000\255\255\255\255\255\255\010\000\
    \009\000\255\255\255\255\255\255\255\255\255\255\003\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\041\000\042\000\043\000\
    \255\255\043\000\255\255\043\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\005\000\255\255\255\255\004\000\003\000\004\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\005\000\255\255\
    \255\255\004\000\003\000\004\000\255\255\255\255\255\255\255\255\
    ";
  Lexing.lex_default = 
   "\001\000\000\000\000\000\255\255\000\000\000\000\255\255\255\255\
    \255\255\255\255\000\000\255\255\000\000\000\000\000\000\000\000\
    \000\000\000\000\255\255\255\255\000\000\000\000\000\000\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\255\255\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\062\000\000\000\000\000\
    \065\000\000\000\068\000\000\000\000\000\255\255\255\255\255\255\
    \255\255\000\000\255\255\000\000\077\000\000\000\080\000\000\000\
    \000\000\255\255\255\255\255\255\255\255\000\000\255\255\000\000\
    ";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\032\000\031\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \032\000\013\000\004\000\012\000\010\000\033\000\000\000\005\000\
    \030\000\029\000\019\000\021\000\026\000\020\000\039\000\018\000\
    \007\000\006\000\006\000\006\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\008\000\017\000\023\000\025\000\024\000\014\000\
    \022\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\028\000\048\000\027\000\009\000\003\000\
    \038\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\016\000\011\000\015\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \037\000\036\000\035\000\034\000\063\000\000\000\000\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\000\000\000\000\000\000\000\000\003\000\000\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\079\000\050\000\000\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\040\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\044\000\046\000\000\000\
    \045\000\049\000\050\000\047\000\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\000\000\042\000\
    \043\000\041\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\049\000\000\000\000\000\000\000\000\000\078\000\000\000\
    \002\000\049\000\000\000\051\000\000\000\000\000\000\000\067\000\
    \060\000\000\000\060\000\000\000\052\000\059\000\059\000\059\000\
    \059\000\059\000\059\000\059\000\059\000\059\000\059\000\000\000\
    \000\000\049\000\054\000\054\000\054\000\054\000\054\000\054\000\
    \054\000\054\000\000\000\051\000\054\000\054\000\054\000\054\000\
    \054\000\054\000\054\000\054\000\052\000\055\000\055\000\055\000\
    \055\000\055\000\055\000\055\000\055\000\055\000\055\000\053\000\
    \053\000\053\000\053\000\053\000\053\000\053\000\053\000\053\000\
    \053\000\066\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \053\000\053\000\053\000\053\000\053\000\053\000\053\000\053\000\
    \053\000\053\000\053\000\053\000\053\000\053\000\053\000\053\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\053\000\
    \053\000\053\000\053\000\053\000\053\000\000\000\000\000\255\255\
    \053\000\053\000\053\000\053\000\053\000\053\000\000\000\000\000\
    \055\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\000\000\000\000\000\000\000\000\000\000\053\000\
    \053\000\053\000\053\000\053\000\053\000\056\000\058\000\000\000\
    \058\000\000\000\000\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\000\000\
    \000\000\000\000\255\255\000\000\000\000\056\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\057\000\
    \059\000\059\000\059\000\059\000\059\000\059\000\059\000\059\000\
    \059\000\059\000\059\000\059\000\059\000\059\000\059\000\059\000\
    \059\000\059\000\059\000\059\000\070\000\069\000\069\000\069\000\
    \069\000\069\000\069\000\069\000\074\000\074\000\074\000\074\000\
    \074\000\074\000\074\000\074\000\074\000\074\000\074\000\074\000\
    \074\000\074\000\074\000\074\000\075\000\075\000\075\000\075\000\
    \075\000\075\000\075\000\075\000\000\000\255\255\000\000\000\000\
    \000\000\000\000\000\000\000\000\071\000\072\000\072\000\072\000\
    \072\000\072\000\072\000\072\000\072\000\072\000\072\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\072\000\072\000\
    \072\000\072\000\072\000\072\000\082\000\081\000\081\000\081\000\
    \081\000\081\000\081\000\081\000\071\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\073\000\073\000\073\000\073\000\073\000\
    \073\000\073\000\073\000\073\000\073\000\000\000\072\000\072\000\
    \072\000\072\000\072\000\072\000\073\000\073\000\073\000\073\000\
    \073\000\073\000\000\000\000\000\083\000\086\000\086\000\086\000\
    \086\000\086\000\086\000\086\000\086\000\086\000\086\000\086\000\
    \086\000\086\000\086\000\086\000\086\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\073\000\073\000\073\000\073\000\
    \073\000\073\000\000\000\000\000\083\000\084\000\084\000\084\000\
    \084\000\084\000\084\000\084\000\084\000\084\000\084\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\084\000\084\000\
    \084\000\084\000\084\000\084\000\085\000\085\000\085\000\085\000\
    \085\000\085\000\085\000\085\000\085\000\085\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\085\000\085\000\085\000\
    \085\000\085\000\085\000\000\000\000\000\000\000\084\000\084\000\
    \084\000\084\000\084\000\084\000\087\000\087\000\087\000\087\000\
    \087\000\087\000\087\000\087\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\085\000\085\000\085\000\
    \085\000\085\000\085\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\255\255\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\011\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\008\000\000\000\000\000\000\000\
    \018\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \019\000\023\000\024\000\030\000\061\000\255\255\255\255\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\255\255\255\255\255\255\255\255\003\000\255\255\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
    \003\000\076\000\006\000\255\255\006\000\006\000\006\000\006\000\
    \006\000\006\000\006\000\006\000\006\000\006\000\009\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\009\000\009\000\255\255\
    \009\000\006\000\007\000\009\000\007\000\007\000\007\000\007\000\
    \007\000\007\000\007\000\007\000\007\000\007\000\255\255\009\000\
    \009\000\009\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\007\000\255\255\255\255\255\255\255\255\076\000\255\255\
    \000\000\006\000\255\255\007\000\255\255\255\255\255\255\064\000\
    \049\000\255\255\049\000\255\255\007\000\049\000\049\000\049\000\
    \049\000\049\000\049\000\049\000\049\000\049\000\049\000\255\255\
    \255\255\007\000\051\000\051\000\051\000\051\000\051\000\051\000\
    \051\000\051\000\255\255\007\000\054\000\054\000\054\000\054\000\
    \054\000\054\000\054\000\054\000\007\000\050\000\050\000\050\000\
    \050\000\050\000\050\000\050\000\050\000\050\000\050\000\052\000\
    \052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\
    \052\000\064\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \052\000\052\000\052\000\052\000\052\000\052\000\053\000\053\000\
    \053\000\053\000\053\000\053\000\053\000\053\000\053\000\053\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\053\000\
    \053\000\053\000\053\000\053\000\053\000\255\255\255\255\061\000\
    \052\000\052\000\052\000\052\000\052\000\052\000\255\255\255\255\
    \055\000\055\000\055\000\055\000\055\000\055\000\055\000\055\000\
    \055\000\055\000\255\255\255\255\255\255\255\255\255\255\053\000\
    \053\000\053\000\053\000\053\000\053\000\055\000\056\000\255\255\
    \056\000\255\255\255\255\056\000\056\000\056\000\056\000\056\000\
    \056\000\056\000\056\000\056\000\056\000\057\000\057\000\057\000\
    \057\000\057\000\057\000\057\000\057\000\057\000\057\000\255\255\
    \255\255\255\255\076\000\255\255\255\255\055\000\058\000\058\000\
    \058\000\058\000\058\000\058\000\058\000\058\000\058\000\058\000\
    \059\000\059\000\059\000\059\000\059\000\059\000\059\000\059\000\
    \059\000\059\000\060\000\060\000\060\000\060\000\060\000\060\000\
    \060\000\060\000\060\000\060\000\066\000\066\000\066\000\066\000\
    \066\000\066\000\066\000\066\000\069\000\069\000\069\000\069\000\
    \069\000\069\000\069\000\069\000\070\000\070\000\070\000\070\000\
    \070\000\070\000\070\000\070\000\074\000\074\000\074\000\074\000\
    \074\000\074\000\074\000\074\000\255\255\064\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\066\000\071\000\071\000\071\000\
    \071\000\071\000\071\000\071\000\071\000\071\000\071\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\071\000\071\000\
    \071\000\071\000\071\000\071\000\078\000\078\000\078\000\078\000\
    \078\000\078\000\078\000\078\000\066\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\072\000\072\000\072\000\072\000\072\000\
    \072\000\072\000\072\000\072\000\072\000\255\255\071\000\071\000\
    \071\000\071\000\071\000\071\000\072\000\072\000\072\000\072\000\
    \072\000\072\000\255\255\255\255\078\000\081\000\081\000\081\000\
    \081\000\081\000\081\000\081\000\081\000\082\000\082\000\082\000\
    \082\000\082\000\082\000\082\000\082\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\072\000\072\000\072\000\072\000\
    \072\000\072\000\255\255\255\255\078\000\083\000\083\000\083\000\
    \083\000\083\000\083\000\083\000\083\000\083\000\083\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\083\000\083\000\
    \083\000\083\000\083\000\083\000\084\000\084\000\084\000\084\000\
    \084\000\084\000\084\000\084\000\084\000\084\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\084\000\084\000\084\000\
    \084\000\084\000\084\000\255\255\255\255\255\255\083\000\083\000\
    \083\000\083\000\083\000\083\000\086\000\086\000\086\000\086\000\
    \086\000\086\000\086\000\086\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\066\000\084\000\084\000\084\000\
    \084\000\084\000\084\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\078\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255";
  Lexing.lex_base_code = 
   "";
  Lexing.lex_backtrk_code = 
   "";
  Lexing.lex_default_code = 
   "";
  Lexing.lex_trans_code = 
   "";
  Lexing.lex_check_code = 
   "";
  Lexing.lex_code = 
   "";
}

let rec token lexbuf =
    __ocaml_lex_token_rec lexbuf 0
and __ocaml_lex_token_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 163 "src/sig_lexer.mll"
          ( let _ = comment lexbuf in token lexbuf )
# 401 "src/sig_lexer.ml"

  | 1 ->
# 164 "src/sig_lexer.mll"
          ( token lexbuf )
# 406 "src/sig_lexer.ml"

  | 2 ->
# 165 "src/sig_lexer.mll"
         ( update_handle_lineno(); token lexbuf )
# 411 "src/sig_lexer.ml"

  | 3 ->
# 166 "src/sig_lexer.mll"
         ( LPAREN )
# 416 "src/sig_lexer.ml"

  | 4 ->
# 167 "src/sig_lexer.mll"
         ( RPAREN )
# 421 "src/sig_lexer.ml"

  | 5 ->
# 168 "src/sig_lexer.mll"
         ( LSQUAREPAREN )
# 426 "src/sig_lexer.ml"

  | 6 ->
# 169 "src/sig_lexer.mll"
         ( RSQUAREPAREN )
# 431 "src/sig_lexer.ml"

  | 7 ->
# 170 "src/sig_lexer.mll"
         ( COMMA )
# 436 "src/sig_lexer.ml"

  | 8 ->
# 171 "src/sig_lexer.mll"
         ( EQ )
# 441 "src/sig_lexer.ml"

  | 9 ->
# 172 "src/sig_lexer.mll"
         ( GT )
# 446 "src/sig_lexer.ml"

  | 10 ->
# 173 "src/sig_lexer.mll"
         (	LT )
# 451 "src/sig_lexer.ml"

  | 11 ->
# 174 "src/sig_lexer.mll"
         ( COMPLEXDENOTE )
# 456 "src/sig_lexer.ml"

  | 12 ->
# 175 "src/sig_lexer.mll"
         ( PLUS )
# 461 "src/sig_lexer.ml"

  | 13 ->
# 176 "src/sig_lexer.mll"
         ( MINUS )
# 466 "src/sig_lexer.ml"

  | 14 ->
# 177 "src/sig_lexer.mll"
         ( MULT )
# 471 "src/sig_lexer.ml"

  | 15 ->
# 178 "src/sig_lexer.mll"
         ( DIV )
# 476 "src/sig_lexer.ml"

  | 16 ->
# 179 "src/sig_lexer.mll"
         ( SEMICOLON )
# 481 "src/sig_lexer.ml"

  | 17 ->
# 180 "src/sig_lexer.mll"
         ( LBRACE )
# 486 "src/sig_lexer.ml"

  | 18 ->
# 181 "src/sig_lexer.mll"
         ( RBRACE )
# 491 "src/sig_lexer.ml"

  | 19 ->
# 182 "src/sig_lexer.mll"
         ( QUESTIONMARK )
# 496 "src/sig_lexer.ml"

  | 20 ->
# 183 "src/sig_lexer.mll"
         (	EXCMARK )
# 501 "src/sig_lexer.ml"

  | 21 ->
# 184 "src/sig_lexer.mll"
         ( NUMBERSIGN )
# 506 "src/sig_lexer.ml"

  | 22 ->
# 185 "src/sig_lexer.mll"
         ( VERTICALBAR )
# 511 "src/sig_lexer.ml"

  | 23 ->
# 186 "src/sig_lexer.mll"
         ( DOLLAR )
# 516 "src/sig_lexer.ml"

  | 24 ->
# 187 "src/sig_lexer.mll"
         ( HAT )
# 521 "src/sig_lexer.ml"

  | 25 ->
# 188 "src/sig_lexer.mll"
         ( DOTEQ )
# 526 "src/sig_lexer.ml"

  | 26 ->
# 189 "src/sig_lexer.mll"
         ( CLKZERO )
# 531 "src/sig_lexer.ml"

  | 27 ->
# 190 "src/sig_lexer.mll"
         (	CLKPLUS )
# 536 "src/sig_lexer.ml"

  | 28 ->
# 191 "src/sig_lexer.mll"
         ( CLKMINUS )
# 541 "src/sig_lexer.ml"

  | 29 ->
# 192 "src/sig_lexer.mll"
         ( CLKMULT )
# 546 "src/sig_lexer.ml"

  | 30 ->
# 193 "src/sig_lexer.mll"
         ( CLKEQ )
# 551 "src/sig_lexer.ml"

  | 31 ->
# 194 "src/sig_lexer.mll"
         ( CLKLTE )
# 556 "src/sig_lexer.ml"

  | 32 ->
# 195 "src/sig_lexer.mll"
         ( CLKGTE )
# 561 "src/sig_lexer.ml"

  | 33 ->
# 196 "src/sig_lexer.mll"
         ( CLKDIFF )
# 566 "src/sig_lexer.ml"

  | 34 ->
# 197 "src/sig_lexer.mll"
         ( DIFF )
# 571 "src/sig_lexer.ml"

  | 35 ->
# 198 "src/sig_lexer.mll"
         ( GTE )
# 576 "src/sig_lexer.ml"

  | 36 ->
# 199 "src/sig_lexer.mll"
         (	LTE )
# 581 "src/sig_lexer.ml"

  | 37 ->
# 200 "src/sig_lexer.mll"
         (	POWER )
# 586 "src/sig_lexer.ml"

  | 38 ->
# 201 "src/sig_lexer.mll"
         ( LPAVER )
# 591 "src/sig_lexer.ml"

  | 39 ->
# 202 "src/sig_lexer.mll"
         ( RPAVER )
# 596 "src/sig_lexer.ml"

  | 40 ->
# 204 "src/sig_lexer.mll"
  ( 
			NUM_INT (Lexing.lexeme lexbuf) 
		)
# 603 "src/sig_lexer.ml"

  | 41 ->
# 208 "src/sig_lexer.mll"
  ( 
			NUM_INT (Lexing.lexeme lexbuf) 
		)
# 610 "src/sig_lexer.ml"

  | 42 ->
# 212 "src/sig_lexer.mll"
  ( 
			NUM_INT (Lexing.lexeme lexbuf)
		)
# 617 "src/sig_lexer.ml"

  | 43 ->
# 216 "src/sig_lexer.mll"
  ( 
			NUM_FLOAT (Lexing.lexeme lexbuf) 
		)
# 624 "src/sig_lexer.ml"

  | 44 ->
# 219 "src/sig_lexer.mll"
          ( CHARACTER_CONST ( chr lexbuf) )
# 629 "src/sig_lexer.ml"

  | 45 ->
# 220 "src/sig_lexer.mll"
         ( STRING_CONST (str lexbuf) )
# 634 "src/sig_lexer.ml"

  | 46 ->
# 222 "src/sig_lexer.mll"
  (
			scan_ident (Lexing.lexeme lexbuf)
		)
# 641 "src/sig_lexer.ml"

  | 47 ->
# 226 "src/sig_lexer.mll"
  (
			EOF
		)
# 648 "src/sig_lexer.ml"

  | 48 ->
# 230 "src/sig_lexer.mll"
  (
			update_handle_line (Lexing.lexeme lexbuf);
			update_handle_pos (Lexing.lexeme_start lexbuf);
			display_error
				(Input_handle.curfile())
				(Input_handle.curlineno())
				(Input_handle.curline())
				(Input_handle.curoutchannel())
				"Invalid symbol";
			token lexbuf
		)
# 663 "src/sig_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; 
      __ocaml_lex_token_rec lexbuf __ocaml_lex_state

and comment lexbuf =
    __ocaml_lex_comment_rec lexbuf 61
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 243 "src/sig_lexer.mll"
       ( () )
# 675 "src/sig_lexer.ml"

  | 1 ->
# 244 "src/sig_lexer.mll"
       (	comment lexbuf )
# 680 "src/sig_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; 
      __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

and str lexbuf =
    __ocaml_lex_str_rec lexbuf 64
and __ocaml_lex_str_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 247 "src/sig_lexer.mll"
          ( "" )
# 692 "src/sig_lexer.ml"

  | 1 ->
# 248 "src/sig_lexer.mll"
               ( let cur = scan_hex_escape (String.sub 
									(Lexing.lexeme lexbuf) 2 2) in cur ^ (str lexbuf) )
# 698 "src/sig_lexer.ml"

  | 2 ->
# 250 "src/sig_lexer.mll"
               ( let cur = scan_oct_escape (String.sub 
									(Lexing.lexeme lexbuf) 1 3) in cur ^ (str lexbuf) )
# 704 "src/sig_lexer.ml"

  | 3 ->
# 252 "src/sig_lexer.mll"
            ( (String.make 1 (Char.chr 0)) ^ (str lexbuf) )
# 709 "src/sig_lexer.ml"

  | 4 ->
# 253 "src/sig_lexer.mll"
            ( let cur = scan_escape (String.sub 
									(Lexing.lexeme lexbuf) 1 1) in cur ^ (str lexbuf) )
# 715 "src/sig_lexer.ml"

  | 5 ->
# 255 "src/sig_lexer.mll"
          ( let cur = Lexing.lexeme lexbuf in cur ^ (str lexbuf) )
# 720 "src/sig_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; 
      __ocaml_lex_str_rec lexbuf __ocaml_lex_state

and chr lexbuf =
    __ocaml_lex_chr_rec lexbuf 76
and __ocaml_lex_chr_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 258 "src/sig_lexer.mll"
           ( "" )
# 732 "src/sig_lexer.ml"

  | 1 ->
# 259 "src/sig_lexer.mll"
               ( let cur = scan_hex_escape (String.sub 
									(Lexing.lexeme lexbuf) 2 2) in cur ^ (chr lexbuf) )
# 738 "src/sig_lexer.ml"

  | 2 ->
# 261 "src/sig_lexer.mll"
               ( let cur = scan_oct_escape (String.sub 
									(Lexing.lexeme lexbuf) 1 3) in cur ^ (chr lexbuf) )
# 744 "src/sig_lexer.ml"

  | 3 ->
# 263 "src/sig_lexer.mll"
            ( (String.make 1 (Char.chr 0)) ^ (chr lexbuf) )
# 749 "src/sig_lexer.ml"

  | 4 ->
# 264 "src/sig_lexer.mll"
            ( let cur = scan_escape (String.sub 
									(Lexing.lexeme lexbuf) 1 1) in cur ^ (chr lexbuf) )
# 755 "src/sig_lexer.ml"

  | 5 ->
# 266 "src/sig_lexer.mll"
          ( let cur = Lexing.lexeme lexbuf in cur ^ (chr lexbuf) )
# 760 "src/sig_lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; 
      __ocaml_lex_chr_rec lexbuf __ocaml_lex_state

;;

# 267 "src/sig_lexer.mll"
 
	

# 771 "src/sig_lexer.ml"
