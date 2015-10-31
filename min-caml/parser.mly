%{
(* parserが利用する変数、関数、型などの定義 *)
open Syntax
let addtyp x = (x, Type.gentyp ())
%}

/* (* 字句を表すデータ型の定義 (caml2html: parser_token) *) */
%token <bool> BOOL
%token <int> INT
%token <float> FLOAT
%token NOT
%token MINUS
%token PLUS
%token AST
%token SLASH
%token XOR
%token OR
%token AND
%token SLL
%token SRL
%token MINUS_DOT
%token PLUS_DOT
%token AST_DOT
%token SLASH_DOT
%token SQRT
%token EQUAL
%token LESS_GREATER
%token LESS_EQUAL
%token GREATER_EQUAL
%token LESS
%token GREATER
%token FEQUAL
%token FLESS
%token IN
%token OUT
%token SET_HP
%token GET_HP
%token IF
%token THEN
%token ELSE
%token <Id.t> IDENT
%token LET
%token IN
%token REC
%token COMMA
%token ARRAY_CREATE
%token ARRAY_CREATE_
%token TO_FLOAT
%token TO_INT
%token TO_ARRAY
%token DOT
%token LESS_MINUS
%token SEMICOLON
%token LPAREN
%token RPAREN
%token EOF

/* (* 優先順位とassociativityの定義（低い方から高い方へ） (caml2html: parser_prior) *) */
%right prec_let
%right SEMICOLON 
%right prec_if
%right LESS_MINUS
%left COMMA
%left EQUAL LESS_GREATER LESS GREATER LESS_EQUAL GREATER_EQUAL
%left PLUS MINUS PLUS_DOT MINUS_DOT
%left AST SLASH AST_DOT SLASH_DOT XOR OR AND
%left SLL SRL
%right prec_unary_minus
%left prec_app
%left DOT

/* (* 開始記号の定義 *) */
%type <Syntax.t> exp
%start exp

%%

simple_exp: /* (* 括弧をつけなくても関数の引数になれる式 (caml2html: parser_simple) *) */
| LPAREN exp RPAREN
    { $2 }
| LPAREN RPAREN
    { Unit }
| BOOL
    { Bool($1) }
| INT
    { Int($1) }
| FLOAT
    { Float($1) }
| IDENT
    { Var($1) }
| simple_exp DOT LPAREN exp RPAREN
    { Get($1, $4) }

exp: /* (* 一般の式 (caml2html: parser_exp) *) */
| simple_exp
    { $1 }
| NOT exp
    %prec prec_app
    { Not($2) }
| MINUS exp
    %prec prec_unary_minus
    { match $2 with
    | Float(f) -> Float(-.f) (* -1.23などは型エラーではないので別扱い *)
    | e -> Neg(e) }
| exp PLUS exp /* (* 足し算を構文解析するルール (caml2html: parser_add) *) */
    { Add($1, $3) }
| exp MINUS exp
    { Sub($1, $3) }
| exp AST exp
    { Mul($1, $3) }
| exp SLASH exp
    { Div($1, $3) }
| exp XOR exp
    { Xor($1, $3) }
| exp OR exp
    { Or($1, $3) }
| exp AND exp
    { And($1, $3) }
| exp SLL exp
    { Sll($1, $3) }
| exp SRL exp
    { Srl($1, $3) }
| exp EQUAL exp
    { Eq($1, $3) }
| exp LESS_GREATER exp
    { Not(Eq($1, $3)) }
| exp LESS exp
    { Not(LE($3, $1)) }
| exp GREATER exp
    { Not(LE($1, $3)) }
| exp LESS_EQUAL exp
    { LE($1, $3) }
| exp GREATER_EQUAL exp
    { LE($3, $1) }
| IF exp THEN exp ELSE exp
    %prec prec_if
    { If($2, $4, $6) }
| MINUS_DOT exp
    %prec prec_unary_minus
    { FNeg($2) }
| exp PLUS_DOT exp
    { FAdd($1, $3) }
| exp MINUS_DOT exp
    { FSub($1, $3) }
| exp AST_DOT exp
    { FMul($1, $3) }
| exp SLASH_DOT exp
    { FDiv($1, $3) }
| LET IDENT EQUAL exp IN exp
    %prec prec_let
    { Let(addtyp $2, $4, $6) }
| LPAREN LET IDENT EQUAL exp RPAREN /* グローバル変数宣言用。Ocamlの文法とは異なるが、結合順序の崩壊を防ぐために、必ず丸括弧でくくる事！ */
    %prec prec_let
    { LetDef(addtyp $3, $5) }
| LET REC fundef IN exp
    %prec prec_let
    { LetRec($3, $5) }
| LPAREN LET REC fundef RPAREN /* グローバル関数宣言用。Ocamlの文法とは異なるが、結合順序の崩壊を防ぐために、必ず丸括弧でくくる事！ */
    { LetRecDef($4) }
| exp actual_args
    %prec prec_app
    { App($1, $2) }
| elems
    { Tuple($1) }
| LET LPAREN pat RPAREN EQUAL exp IN exp
    { LetTuple($3, $6, $8) }
| simple_exp DOT LPAREN exp RPAREN LESS_MINUS exp
    { Put($1, $4, $7) }
| exp SEMICOLON exp
    { Let((Id.gentmp Type.Unit, Type.Unit), $1, $3) }
| exp SEMICOLON
    { $1 }
| ARRAY_CREATE simple_exp simple_exp
    %prec prec_app
    { Array($2, $3) }
| ARRAY_CREATE_ simple_exp simple_exp
    %prec prec_app
    { Array($2, $3) }
| TO_FLOAT simple_exp
    %prec prec_app
    { ToFloat($2) }
| TO_INT simple_exp
    %prec prec_app
    { ToInt($2) }
| TO_ARRAY simple_exp
    %prec prec_app
    { ToArray($2) }
| FEQUAL simple_exp simple_exp
    %prec prec_app
    { Eq($2, $3) }
| FLESS simple_exp simple_exp
    %prec prec_app
    { LE($2, $3) }
| SQRT simple_exp
    %prec prec_app
    { Sqrt($2) }
| IN simple_exp
    %prec prec_app
    { In($2) }
| OUT simple_exp
    %prec prec_app
    { Out($2) }
| SET_HP simple_exp
    %prec prec_app
    { SetHp($2) }
| GET_HP simple_exp
    %prec prec_app
    { GetHp($2) }
| error
    { failwith
	(Printf.sprintf "parse error near line %d column %d"
  !Lexer.line
	   ((Parsing.symbol_start ()) - !Lexer.char)) }

fundef:
| IDENT formal_args EQUAL exp
    { { name = addtyp $1; args = $2; body = $4 } }

formal_args:
| IDENT formal_args
    { addtyp $1 :: $2 }
| IDENT
    { [addtyp $1] }

actual_args:
| actual_args simple_exp
    %prec prec_app
    { $1 @ [$2] }
| simple_exp
    %prec prec_app
    { [$1] }

elems:
| elems COMMA exp
    { $1 @ [$3] }
| exp COMMA exp
    { [$1; $3] }

pat:
| pat COMMA IDENT
    { $1 @ [addtyp $3] }
| IDENT COMMA IDENT
    { [addtyp $1; addtyp $3] }
