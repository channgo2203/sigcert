type token =
  | EVENT
  | BOOL
  | SHORT
  | INT
  | LONG
  | REAL
  | COMPLEX
  | CHAR
  | STRING
  | ENUM
  | STRUCT
  | BUNDLE
  | TRUE
  | FALSE
  | CONSTANT
  | SHARED
  | STATEVAR
  | TYPE
  | PROCESS
  | ACTION
  | NODE
  | FUNCTION
  | SAFE
  | DETERMINISTIC
  | UNSAFE
  | SPEC
  | INIT
  | PRAGMAS
  | END
  | EOF
  | LPAREN
  | RPAREN
  | LSQUAREPAREN
  | RSQUAREPAREN
  | COMMA
  | SEMICOLON
  | LBRACE
  | RBRACE
  | QUESTIONMARK
  | EXCMARK
  | NUMBERSIGN
  | VERTICALBAR
  | DOLLAR
  | WINDOW
  | DEFAULT
  | WHEN
  | CELL
  | DOTEQ
  | HAT
  | CLKZERO
  | CLKPLUS
  | CLKMINUS
  | CLKMULT
  | CLKEQ
  | CLKLTE
  | CLKGTE
  | CLKDIFF
  | NOT
  | OR
  | AND
  | XOR
  | EQ
  | DIFF
  | GT
  | GTE
  | LT
  | LTE
  | PLUS
  | MINUS
  | MULT
  | DIV
  | MODULO
  | POWER
  | COMPLEXDENOTE
  | IF
  | THEN
  | ELSE
  | LPAVER
  | RPAVER
  | WHERE
  | EXTERNAL
  | NUM_INT of (string)
  | NUM_FLOAT of (string)
  | NUM_COMPLEX of (string*string)
  | CHARACTER_CONST of (string)
  | STRING_CONST of (string)
  | IDENTIFIER of (string)
  | COMMENT

val interpret :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Sig_abs.sig_file
val file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Sig_abs.sig_file
