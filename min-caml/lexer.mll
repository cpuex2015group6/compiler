{
(* lexerが利用する変数、関数、型などの定義 *)
open Parser
open Type
let line = ref 1
let char = ref 0
}

(* 正規表現の略記 *)
let space = [' ' '\t' '\n' '\r']
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']

rule token = parse
| space+
    { (let count = ref 0 in
        String.iter (fun x ->
                     (if x = '\n' then
                       (line := !line + 1;
                        char := !count + (Lexing.lexeme_start lexbuf))
                      else
                        ());
                     count := !count + 1)
                    (Lexing.lexeme lexbuf));
        token lexbuf }
| "(*"
    { comment lexbuf; (* ネストしたコメントのためのトリック *)
      token lexbuf }
| '('
    { LPAREN }
| ')'
    { RPAREN }
| "true"
    { BOOL(true) }
| "false"
    { BOOL(false) }
| "not"
    { NOT }
| digit+ (* 整数を字句解析するルール (caml2html: lexer_int) *)
    { INT(int_of_string (Lexing.lexeme lexbuf)) }
| digit+ ('.' digit*)? (['e' 'E'] ['+' '-']? digit+)?
    { FLOAT(float_of_string (Lexing.lexeme lexbuf)) }
| '-' (* -.より後回しにしなくても良い? 最長一致? *)
    { MINUS }
| '+' (* +.より後回しにしなくても良い? 最長一致? *)
    { PLUS }
| '*'
    { AST }
| '/'
    { SLASH }
| "lxor"
    { XOR }
| "lor"
    { OR }
| "land"
    { AND }
| "lsl"
    { SLL }
| "lsr"
    { SRL }
| "-."
    { MINUS_DOT }
| "+."
    { PLUS_DOT }
| "*."
    { AST_DOT }
| "/."
    { SLASH_DOT }
| "sqrt"
    { SQRT }
| '='
    { EQUAL }
| "<>"
    { LESS_GREATER }
| "<="
    { LESS_EQUAL }
| ">="
    { GREATER_EQUAL }
| '<'
    { LESS }
| '>'
    { GREATER }
| "if"
    { IF }
| "then"
    { THEN }
| "else"
    { ELSE }
| "let"
    { LET }
| "in"
    { IN }
| "rec"
    { REC }
| ','
    { COMMA }
| '_'
    { IDENT(Id.gentmp Type.Unit) }
| "Array.create" (* [XX] ad hoc *)
    { ARRAY_CREATE }
| "create_array"
    { ARRAY_CREATE }
| "i2f"
    { I2F }
| "f2i"
    { F2I }
| "i2ia"
    { I2IA }
| "i2fa"
    { I2FA }
| "a2i"
    { A2I }
| "fequal"
    { FEQUAL }
| "fless"
    { FLESS }
| "input"
    { INPUT }
| "output"
    { OUTPUT }
| "set_hp"
    { SET_HP }
| "get_hp"
    { GET_HP }
| '.'
    { DOT }
| "<-"
    { LESS_MINUS }
| ';'
    { SEMICOLON }
| eof
    { EOF }
| lower (digit|lower|upper|'_')* (* 他の「予約語」より後でないといけない *)
    { IDENT(Lexing.lexeme lexbuf) }
| _
    { failwith
	(Printf.sprintf "unknown token %s near characters %d-%d"
	   (Lexing.lexeme lexbuf)
	   (Lexing.lexeme_start lexbuf)
	   (Lexing.lexeme_end lexbuf)) }
and comment = parse
| "*)"
    { () }
| "(*"
    { comment lexbuf;
      comment lexbuf }
| eof
    { Format.eprintf "warning: unterminated comment@." }
| _
    { comment lexbuf }
