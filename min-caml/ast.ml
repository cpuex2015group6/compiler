(* print AST *)

open Syntax

let rec g indent e = (* AST表示ルーチン *)
  match e with
  | Unit ->
     print_string indent;
     print_string "Unit\n"
  | Bool(v) -> 
     print_string indent;
     print_string "Bool\n";
     print_string (indent^"  ");
     (match v with
     | true -> print_string "true"
     | false -> print_string "false");
     print_string "\n"
  | Int(v) -> 
     print_string indent;
     print_string "Int\n";
     print_string (indent ^ "  ");
     print_int v;
     print_string "\n"
  | Float(v) -> 
     print_string indent;
     print_string "Float\n";
     print_string (indent ^ "  ");
     print_float v;
     print_string "\n";
  | Not(e) ->
     print_string indent;
     print_string "Not\n";
     g (indent ^ "  ") e
  | Neg(e) ->
     print_string indent;
     print_string "Neg\n";
     g (indent ^ "  ") e
  | Add(e1, e2) ->
     print_string indent;
     print_string "Add\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | Sub(e1, e2) ->
     print_string indent;
     print_string "Sub\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | Mul(e1, e2) ->
     print_string indent;
     print_string "Mul\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | Div(e1, e2) ->
     print_string indent;
     print_string "Div\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | Xor(e1, e2) ->
     print_string indent;
     print_string "Xor\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | Or(e1, e2) ->
     print_string indent;
     print_string "Or\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | And(e1, e2) ->
     print_string indent;
     print_string "And\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | Sll(e1, e2) ->
     print_string indent;
     print_string "Sll\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | Srl(e1, e2) ->
     print_string indent;
     print_string "Srl\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | FNeg(e) ->
     print_string indent;
     print_string "FNeg\n";
     g (indent ^ "  ") e;
  | FAdd(e1, e2) ->
     print_string indent;
     print_string "FAdd\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | FSub(e1, e2) ->
     print_string indent;
     print_string "FSub\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | FMul(e1, e2) ->
     print_string indent;
     print_string "FMul\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | FDiv(e1, e2) ->
     print_string indent;
     print_string "FDiv\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | Sqrt(e1) ->
     print_string indent;
     print_string "Sqrt\n";
     g (indent ^ "  ") e1
  | Eq(e1, e2) ->
     print_string indent;
     print_string "Eq\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | LE(e1, e2) ->
     print_string indent;
     print_string "LE\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | If(e1, e2, e3) ->
     print_string indent;
     print_string "If\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2;
     g (indent ^ "  ") e3
  | Let((x, t), e1, e2) ->
     print_string indent;
     print_string "Let\n";
     print_string (indent ^ "  ");
     print_string x;
     print_string "\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | LetDef((x, t), e1) ->
     print_string indent;
     print_string "LetDef\n";
     print_string (indent ^ "  ");
     print_string x;
     print_string "\n";
     g (indent ^ "  ") e1;
  | Var(x) ->
     print_string indent;
     print_string "Var\n";
     print_string (indent ^ "  ");
     print_string x;
     print_string "\n"
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
     print_string indent;
     print_string "LetRec\n";
     print_string (indent ^ "  ");
     print_string x;
     print_string "\n";
     print_string (indent ^ "  ");
     let rec print_list = function 
       | [] -> ()
       | e::l -> print_string e ; print_string " " ; print_list l;
     in
     print_list (List.map (fun (x, t) -> x) yts);
     print_string "\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | LetRecDef({ name = (x, t); args = yts; body = e1 }) ->
     print_string indent;
     print_string "LetRecDef\n";
     print_string (indent ^ "  ");
     print_string x;
     print_string "\n";
     print_string (indent ^ "  ");
     let rec print_list = function 
       | [] -> ()
       | e::l -> print_string e ; print_string " " ; print_list l;
     in
     print_list (List.map (fun (x, t) -> x) yts);
     print_string "\n";
     g (indent ^ "  ") e1
  | App(e, es) -> (* 関数適用の型推論 (caml2html: typing_app) *)
     print_string indent;
     print_string "App\n";
     g (indent ^ "  ") e;
     let rec print_list = function 
       | [] -> ()
       | e::l -> g (indent ^ "  ") e; print_list l;
     in
     print_list es
  | Tuple(es) ->
     print_string indent;
     print_string "Tuple\n";
     let rec print_list = function 
       | [] -> ()
       | e::l -> g (indent ^ "  ") e; print_list l;
     in
     print_list es
  | LetTuple(xts, e1, e2) ->
     print_string indent;
     print_string "LetTuple\n";
     let rec print_list = function 
       | [] -> ()
       | e::l -> print_string e ; print_string " " ; print_list l
     in
     print_list (List.map (fun (x, t) -> x) xts);
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | Array(e1, e2) ->
     print_string indent;
     print_string "Array\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | I2F(e1) ->
     print_string indent;
     print_string "I2F\n";
     g (indent ^ "  ") e1;
  | F2I(e1) ->
     print_string indent;
     print_string "F2I\n";
     g (indent ^ "  ") e1;
  | I2IA(e1) ->
     print_string indent;
     print_string "I2IA\n";
     g (indent ^ "  ") e1;
  | I2FA(e1) ->
     print_string indent;
     print_string "I2FA\n";
     g (indent ^ "  ") e1;
  | A2I(e1) ->
     print_string indent;
     print_string "A2I\n";
     g (indent ^ "  ") e1;
  | In(e1) ->
     print_string indent;
     print_string "In\n";
     g (indent ^ "  ") e1;
  | Out(e1) ->
     print_string indent;
     print_string "Out\n";
     g (indent ^ "  ") e1;
  | Count ->
     print_string indent;
     print_string "Count\n";
  | ShowExec ->
     print_string indent;
     print_string "ShowExec\n";
  | SetCurExec ->
     print_string indent;
     print_string "SetCurExec\n";
  | GetExecDiff ->
     print_string indent;
     print_string "GetExecDiff\n";
  | SetHp(e1) ->
     print_string indent;
     print_string "SetHp\n";
     g (indent ^ "  ") e1;
  | GetHp(e1) ->
     print_string indent;
     print_string "GetHp\n";
     g (indent ^ "  ") e1;
  | Get(e1, e2) ->
     print_string indent;
     print_string "Get\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | Put(e1, e2, e3) ->
     print_string indent;
     print_string "Put\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2

let f e =
  g "" e;
  e
