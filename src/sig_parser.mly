/*
 * Description : parser of Signal
 * Copyright   : (c) Chan Ngo 2013
 * License     : All Rights Reserved
 * Maintainer  : Chan Ngo <chan.ngo@inria.fr>
 */
%{
open Sig_abs
open Ptree
open Exceptions

%}
%token EVENT
%token BOOL
%token SHORT
%token INT
%token LONG
%token REAL
%token COMPLEX
%token CHAR
%token STRING
%token ENUM
%token STRUCT
%token BUNDLE
%token TRUE
%token FALSE
%token CONSTANT
%token SHARED
%token STATEVAR
%token TYPE
%token PROCESS
%token ACTION
%token NODE
%token FUNCTION
%token SAFE
%token DETERMINISTIC
%token UNSAFE
%token SPEC
%token INIT
%token PRAGMAS
%token END
%token EOF
%token LPAREN
%token RPAREN
%token LSQUAREPAREN
%token RSQUAREPAREN
%token COMMA
%token SEMICOLON
%token LBRACE
%token RBRACE
%token QUESTIONMARK
%token EXCMARK
%token NUMBERSIGN
%token VERTICALBAR
%token DOLLAR
%token WINDOW
%token DEFAULT
%token WHEN
%token CELL
%token DOTEQ
%token HAT
%token CLKZERO
%token CLKPLUS
%token CLKMINUS
%token CLKMULT
%token CLKEQ
%token CLKLTE
%token CLKGTE
%token CLKDIFF
%token NOT
%token OR
%token AND
%token XOR
%token EQ
%token DIFF
%token GT
%token GTE
%token LT
%token LTE
%token PLUS
%token MINUS
%token MULT
%token DIV
%token MODULO
%token POWER
%token COMPLEXDENOTE
%token IF
%token THEN
%token ELSE
%token LPAVER
%token RPAVER
%token WHERE
%token EXTERNAL
%token <string> NUM_INT
%token <string> NUM_FLOAT
%token <string*string> NUM_COMPLEX
%token <string> CHARACTER_CONST
%token <string> STRING_CONST
%token <string> IDENTIFIER
%token COMMENT
%token EOF

%nonassoc IF
%nonassoc THEN
%nonassoc ELSE

%right DOTEQ CLKEQ
%left CLKPLUS CLKMINUS
%left CLKMULT
%left CLKGTE CLKLTE CLKDIFF
%left DEFAULT
%left WHEN
%left OR XOR
%left AND
%left NOT
%left EQ DIFF
%nonassoc EQ_INIT
%left GTE GT LT LTE 
%left PLUS MINUS
%left MULT DIV MODULO
%left DOLLAR WINDOW
%nonassoc DOLLAR_INIT WINDOW_INIT
%left CELL
%nonassoc CELL_INIT
%nonassoc INIT
%left UPLUS UMINUS
%left POWER
%left NUMBERSIGN COMPLEXDENOTE
%left HAT
%right RSQUAREPAREN
%right RBRACE
%right RPAREN
%left LSQUAREPAREN
%left LBRACE
%left LPAREN 

/* Non-terminal information */
%start interpret file
%type <Sig_abs.sig_file> file interpret

%%

/* file consists of a process list and a process hierarchy */
interpret:
	file EOF
	{
		$1
	}
;

file:
	/* empty */
	{
		([],Ptree.EMPTY)
	}
| process_decl
	{
		let (procl,sig_ltree) = $1 in
		(procl,List.hd sig_ltree)
	}
| process_decl SEMICOLON
	{
		let (procl,sig_ltree) = $1 in
		(procl,List.hd sig_ltree)
	}
;

/* definition of a process */
process_decl:
	PROCESS IDENTIFIER EQ parameters interface directives p_expr
	{
		let (invars, outvars) = $5 and (leq,lloc,ltdef,lhprocl,lprocl,ptree) = $7 in	
		let currentproc = 
			{ name = $2;
				paramenters = $4;
				inputs = invars;
				outputs = outvars;
				locals = lloc;
				typedefs = ltdef;
				equations = leq;
				hiddenprocs = lhprocl;
			}
		in match ptree with
		| [] -> (currentproc::lprocl, [make_leaf $2])
		| _ -> (currentproc::lprocl, [make_node $2 ptree])
	}
;

/* parameters */
parameters:
	/* empty */
	{
		[]
	}
| LBRACE LBRACE 
	{ 
		[]
	}
|	LBRACE s_declarations RBRACE 
	{ 
		let paras = $2 in 
		List.map (function (t,namelist) -> VARDEF((VAR_PARAMETER,T_CONST(t),namelist))) paras
	}
| LBRACE s_declarations SEMICOLON RBRACE 
	{
		let paras = $2 in 
		List.map (function (t,namelist) -> VARDEF((VAR_PARAMETER,T_CONST(t),namelist))) paras
	}
;

/* interface: inputs + outputs */
interface:
	LPAREN inputs outputs RPAREN
	{
		($2,$3)
	}
;

inputs:
	/* empty */
	{
		[]
	}
|	QUESTIONMARK
	{
		[]
	}
| QUESTIONMARK s_declarations
	{
		let invars = $2 in 
		List.map (function (t,namelist) -> VARDEF((VAR_INPUT,t,namelist))) invars
	}
|	QUESTIONMARK s_declarations SEMICOLON 
	{ 
		let invars = $2 in 
		List.map (function (t,namelist) -> VARDEF((VAR_INPUT,t,namelist))) invars
	}
;

outputs:
	/* empty */
	{
		[]
	}
|	EXCMARK 
	{ 
		[]
	}
| EXCMARK s_declarations 
	{ 
		let outvars = $2 in 
		List.map (function (t,namelist) -> VARDEF((VAR_OUTPUT,t,namelist))) outvars
	}
|	EXCMARK s_declarations SEMICOLON 
	{ 
		let outvars = $2 in 
		List.map (function (t,namelist) -> VARDEF((VAR_OUTPUT,t,namelist))) outvars
	}
;

/* difinition of variable, e.g. integer x, y, z */
s_declarations:
	s_declaration 
	{ 
		[$1]
	}
|	s_declarations SEMICOLON s_declaration 
	{ 
		$1 @ [$3]
	}
;

s_declaration:
  signaltype seq_defs 
	{
		($1,$2)
	}
;

/* variable names */
seq_defs:
	seq_def
	{
		[$1]
	}
|	seq_defs COMMA seq_def 
	{ 
		$1 @ [$3]
	}
;
seq_def:
	IDENTIFIER
	{
		($1,S_NOTHING)
	}
|	IDENTIFIER INIT s_expr 
	{ 
		($1,$3)
	}
;

/* directives */
directives:
	/* empty */
	{
	}
| PRAGMAS END PRAGMAS
	{
	}
|	PRAGMAS pragma_elements END PRAGMAS 
	{
	}
;

pragma_elements:
	pragma_element
	{
	}
|	pragma_elements pragma_element 
	{ 
	}
;

pragma_element:
	IDENTIFIER 
	{
	}
| IDENTIFIER LBRACE pragma_objects RBRACE 
	{ 
	}
|	IDENTIFIER LBRACE pragma_objects RBRACE STRING_CONST 
	{ 
	}
;

pragma_objects:
	IDENTIFIER 
	{
	}
|	pragma_objects IDENTIFIER  
	{ 
	}
;

/* process body */
p_exprs:
	p_expr
	{
		$1
	}
|	p_exprs VERTICALBAR p_expr
	{
		let (leq,lloc,ltdef,lhprocl,lprocl,_) = $1 and (eq,loc,tdef,hprocl,procl,_) = $3 in
		(leq@eq,lloc@loc,ltdef@tdef,lhprocl@hprocl,lprocl@procl,[])
	}
;

/* sig_def, e.g. x := y default z, clock_def, e.g. x ^= y ^= z, x ^< y */
p_expr:
	general_process
	{
		$1
	}
| sig_def
	{
		([$1],[],[],[],[],[])
	}
| clock_def
	{
		([$1],[],[],[],[],[])
	}
;

/* general process: process P= {...}(...) (|...|) */
general_process:
	composition 
	{ 
		$1
	}
| hidden_process
	{
		$1
	}
|	confined_process 
	{ 
		$1
	}
;

composition:
	LPAVER p_exprs RPAVER 
	{ 
		$2
	}
;

hidden_process:
	general_process DIV seq_names
	{
		let (leq,lloc,ltdef,lhprocl,lprocl,_) = $1 in
		let hiddenproc = 
			{
				hiddenlocals = $3;
				hiddenequations = leq;
			} 
		in ([],[],[],[hiddenproc],[],[])
	}
;

seq_names:
	IDENTIFIER
	{
		[($1,S_NOTHING)]
	}
| seq_names COMMA IDENTIFIER
	{
		$1 @ [($3,S_NOTHING)]
	}
;

confined_process:
	general_process decleration_blk 
	{ 
		let (leq,lloc,ltdef,lhprocl,lprocl,_) = $1
		and (loc,tdef,procl,ptree) = $2 in
		(leq,loc@lloc,tdef@ltdef,lhprocl,procl@lprocl,ptree)
	}
;

decleration_blk:
	WHERE declarations END 
	{ 
		$2
	}
|	WHERE declarations SEMICOLON END 
	{ 
		$2
	}
;
/* declarations inside where...end block */
declarations:
	declaration 
	{ 
		$1
	}
|	declarations SEMICOLON declaration 
	{ 
		let (lloc,ltdef,lprocl,lptree) = $1 
		and (loc,tdef,procl,ptree) = $3 in
		((lloc@loc),(ltdef@tdef),(lprocl@procl),(lptree@ptree))
	}
;

declaration:
	s_declaration
	{
		let (t,namelist) = $1 in
		([VARDEF(VAR_LOCAL,t,namelist)],[],[],[])
	}
| declaration_types
	{
		([],$1,[],[])
	}
| declaration_constants
	{
		([$1],[],[],[])
	}
| process_decl
	{
		let (procl,ptree) = $1 in
		([],[],procl,ptree)
	}
;

/* signal definition */
sig_def:
	s_expr DOTEQ s_expr 
	{ 
		SIGDEF($1,$3)
	}
| process_call
	{
		SIGDEF(S_NOTHING,$1)
	}
;

/* clock constraint definition */
clock_def:
	sexpr_eq 
	{ 
		CLKCONS($1)
	}
| s_expr CLKLTE s_expr 
	{
		CLKCONS(S_CLKLTE($1,$3)) 
	}
| s_expr CLKGTE s_expr 
	{
		CLKCONS(S_CLKGTE($1,$3))
	}
| s_expr CLKDIFF s_expr 
	{
		CLKCONS(S_CLKDIFF($1,$3))
	}
;

sexpr_eq:
	sexpr_eq CLKEQ s_expr 
	{ 
		match $1 with
		| S_CLKEQ(l) -> S_CLKEQ(l@[$3])
		| _ -> S_NOTHING
	}
|	s_expr CLKEQ s_expr 
	{ 
		S_CLKEQ([$1;$3])
	}
;

/* declaration of types */
declaration_types:
	TYPE definition_types 
	{ 
		$2
	}
;

definition_types:
	definition_types COMMA definition_type 
	{ 
		$1 @ [$3]
	}
| definition_type 
	{ 
		[$1]
	}
;

definition_type:
	IDENTIFIER EQ external_notation INIT IDENTIFIER 
	{ 
		TYPEDEF(T_EXTERNAL($3),($1,S_CONSTANT(S_STRING($5))))
	}
| IDENTIFIER EQ external_notation %prec EQ_INIT
	{ 
		TYPEDEF(T_EXTERNAL($3),($1,S_NOTHING))
	}
| IDENTIFIER EQ signaltype 
	{ 
		TYPEDEF($3,($1,S_NOTHING))
	}
|	IDENTIFIER 
	{ 
		TYPEDEF(NO_TYPE,($1,S_NOTHING))
	}
	/* enum type declaration */
| IDENTIFIER EQ ENUM LPAREN enumelements RPAREN 
	{ 
		TYPEDEF(T_ENUM($1,$5),($1,S_NOTHING))
	}
;
/* enum items */
enumelements:
	enumelements COMMA IDENTIFIER 
	{ 
		$1 @ [$3] 
	}
| IDENTIFIER 
	{ 
		[$1]
	}
;

/* declaration of constant */
declaration_constants:
	CONSTANT signaltype definition_constants
	{ 
		VARDEF(VAR_LOCAL,T_CONST($2),$3)
	}
;

definition_constants:
	definition_constants COMMA definition_constant 
	{ 
		$1 @ [$3]
	}
|	definition_constant 
	{
		[$1]
	}
;

definition_constant:
	IDENTIFIER EQ external_notation 
	{ 
		($1,S_VAR($3))
	}
| IDENTIFIER EQ s_expr 
	{ 
		($1,$3)
	}
|	IDENTIFIER 
	{ 
		($1,S_NOTHING)
	}
;

/* signal expressions */
s_expr:
	IDENTIFIER 
	{ 
		S_VAR($1)
	}
|	TRUE 
	{ 
		S_CONSTANT(S_TRUE)
	}
| FALSE 
	{ 
		S_CONSTANT(S_FALSE)
	}
| NUM_INT 
	{ 
		S_CONSTANT(S_INT($1))
	}
| NUM_FLOAT 
	{ 
		S_CONSTANT(S_REAL($1))
	}
/* the string representation of a character, e.g. "\017", "2" */
| CHARACTER_CONST 
	{ 
		S_CONSTANT(S_CHAR($1))
	}
| STRING_CONST 
	{ 
		S_CONSTANT(S_STRING($1))
	}
| NUMBERSIGN IDENTIFIER 
	{ 
		S_ENUMITEM("",S_CONSTANT(S_STRING($2)))
	}
|	IDENTIFIER NUMBERSIGN IDENTIFIER 
	{ 
		S_ENUMITEM($1,S_CONSTANT(S_STRING($3)))
	}
| IDENTIFIER LSQUAREPAREN s_expr RSQUAREPAREN
	{
		S_ARRAYITEM($1,$3)
	}
	/** casting: base_type * expression */
| scalartype LPAREN s_expr RPAREN 
	{ 
		 S_CAST($1,$3)
	}
	/** dynamic operations */
| s_expr DOLLAR %prec DOLLAR_INIT
	{
		S_DELAY($1)
	}
| s_expr DOLLAR s_expr %prec DOLLAR_INIT
	{
		S_DELAYBY($1,$3)
	}
| s_expr DOLLAR INIT s_expr
	{
		S_DELAYINIT($1,$4)
	}
| s_expr DOLLAR s_expr INIT s_expr
	{
		S_DELAYBYINIT($1,$3,$5)
	}
| s_expr WINDOW s_expr %prec WINDOW_INIT
	{
		S_WINDOW($1,$3)
	}
| s_expr WINDOW s_expr INIT s_expr
	{
		S_WINDOWINIT($1,$3,$5)
	}
	/** temporal operators */
| s_expr CELL s_expr %prec CELL_INIT
	{
		S_CELL($1,$3)
	}
| s_expr CELL s_expr INIT s_expr
	{
		S_CELLINIT($1,$3,$5)
	}
| s_expr DEFAULT s_expr 
	{ 
		S_DEFAULT($1,$3)
	}
|	s_expr WHEN s_expr 
	{ 
		S_WHEN($1,$3)
	}
	/** clock operators */
| CLKZERO 
	{
		S_CLKZERO 
	}
| HAT s_expr
	{
		S_CLKHAT($2)
	}
|	WHEN s_expr 
	{ 
		S_CLKWHEN($2)
	}
| s_expr CLKPLUS s_expr 
	{ 
		S_CLKPLUS($1,$3)
	}
| s_expr CLKMINUS s_expr 
	{ 
		S_CLKMINUS($1,$3)
	}
| s_expr CLKMULT s_expr 
	{ 
		S_CLKMULT($1,$3)
	}
	/* unary and binary operators */
| NOT s_expr 
	{ 
		S_UNARY(S_NOT,$2)
	}
|	s_expr OR s_expr 
	{ 
		S_BINARY(S_OR,$1,$3)
	}
| s_expr AND s_expr 
	{ 
		S_BINARY(S_AND,$1,$3)
	}
| s_expr XOR s_expr 
	{ 
		S_BINARY(S_XOR,$1,$3)
	}
| s_expr EQ s_expr 
	{ 
		S_BINARY(S_EQ,$1,$3)
	}
| s_expr DIFF s_expr 
	{ 
		S_BINARY(S_DIFF,$1,$3)
	}
| s_expr GT s_expr 
	{ 
		S_BINARY(S_GT,$1,$3)
	}
| s_expr GTE s_expr 
	{ 
		S_BINARY(S_GTE,$1,$3)
	}
| s_expr LT s_expr 
	{ 
		S_BINARY(S_LT,$1,$3)
	}
| s_expr LTE s_expr 
	{ 
		S_BINARY(S_LTE,$1,$3)
	}
| s_expr PLUS s_expr 
	{ 
		S_BINARY(S_PLUS,$1,$3)
	}
|	s_expr MINUS s_expr 
	{ 
		S_BINARY(S_MINUS,$1,$3)
	}
| s_expr MULT s_expr 
	{ 
		S_BINARY(S_MULT,$1,$3)
	}
| s_expr DIV s_expr 
	{ 
		S_BINARY(S_DIV,$1,$3)
	}
| s_expr MODULO s_expr 
	{ 
		S_BINARY(S_MODULO,$1,$3)
	}
| s_expr POWER s_expr 
	{ 
		S_BINARY(S_POWER,$1,$3)
	}
| s_expr COMPLEXDENOTE s_expr 
	{ 
		S_BINARY(S_COPLEXDENOTE,$1,$3)
	}
| PLUS s_expr %prec UPLUS 
	{ 
		S_UNARY(S_UPLUS,$2)
	}
| MINUS s_expr %prec UMINUS 
	{ 
		S_UNARY(S_UMINUS,$2)
	}
	/* if */
| IF s_expr THEN s_expr ELSE s_expr 
	{ 
		S_IF($2,$4,$6)
	}
	/* close parent expr */
| LPAREN s_expr RPAREN
	{
		S_PCLOSE($2)
	}
	/* tuples */
| LPAREN s_exprs COMMA s_expr RPAREN 
	{ 
		S_TUPLES($2 @ [$4])
	}
	/* process calls */
| process_call
	{
		$1
	}
;

/* process calls */
process_call:
 	IDENTIFIER LPAREN RPAREN 
	{ 
		S_PROCESSCALL($1,[],[],[])
	}
| IDENTIFIER LBRACE RBRACE 
	{ 
		S_PROCESSCALL($1,[],[],[])
	}
| IDENTIFIER LBRACE s_exprs RBRACE 
	{ 
		S_PROCESSCALL($1,$3,[],[])
	}
| IDENTIFIER LPAREN s_exprs RPAREN
	{
		S_PROCESSCALL($1,[],$3,[])
	}
| IDENTIFIER LBRACE RBRACE LPAREN RPAREN
	{
		S_PROCESSCALL($1,[],[],[])
	}
| IDENTIFIER LBRACE s_exprs RBRACE LPAREN RPAREN
	{
		S_PROCESSCALL($1,$3,[],[])
	}
|	IDENTIFIER LBRACE RBRACE LPAREN s_exprs RPAREN
	{
		S_PROCESSCALL($1,[],$5,[])
	}
| IDENTIFIER LBRACE s_exprs RBRACE LPAREN s_exprs RPAREN
	{
		S_PROCESSCALL($1,$3,$6,[])
	}
;

/* list of expressions */
s_exprs:
	s_expr
	{
		[$1]
	}
|	s_exprs COMMA s_expr
	{
		$1 @ [$3]
	}
;

/* signal base types */
signaltype:
	/* including typedef (enum, struct, bundle,...) and external types */
	IDENTIFIER 
	{ 
		T_NAMED_TYPED($1)
	}
|	scalartype 
	{ 
		$1
	}
| arraytype 
	{ 
		$1
	}
;
/* scalartype: event, bool, short, int, real, complex */
scalartype:
	EVENT 
	{
		T_EVENT
	}
| BOOL 
	{
		T_BOOL
	}
| SHORT 
	{
		T_INT(SHORT,SIGNED)
	}
| INT 
	{
		T_INT(NO_SIZE,SIGNED)
	}
| LONG 
	{
		T_INT(LONG,SIGNED)
	}
| REAL 
	{
		T_REAL
	}
| COMPLEX 
	{
		T_COMPLEX
	}
| CHAR 
	{
		T_CHAR(UNSIGNED)
	}
| STRING 
	{
		T_STRING
	}
;
/* array type: sizes and type */
arraytype:
  LSQUAREPAREN arraysizes RSQUAREPAREN signaltype 
	{
		T_ARRAY($4,$2)
	}
;

arraysizes:
	s_expr 
	{
		[$1] 
	}
|	arraysizes COMMA s_expr 
	{ 
		$1 @ [$3]
	}
;

external_notation:
	EXTERNAL STRING_CONST 
	{ 
		$2
	}
;

%%
