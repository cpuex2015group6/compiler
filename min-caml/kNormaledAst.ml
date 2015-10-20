(* print kNormaledAST K正規化後のASTを表示する *)

open KNormal

let rec g indent e = (* AST表示ルーチン *)
  match e with
  | Unit ->
     print_string (indent ^ "Unit\n")
  | Int(v) -> 
     print_string (indent ^ "Int ");
     print_int v;
     print_string "\n"
  | Float(v) -> 
     print_string (indent ^ "Float ");
     print_float v;
     print_string "\n"
  | Neg(e) ->
     print_string (indent ^ "Neg " ^ e ^ "\n")
  | Add(e1, e2) ->
     print_string (indent ^ "Add " ^ e1 ^ " " ^ e2 ^ "\n")
  | Sub(e1, e2) ->
     print_string (indent ^ "Sub " ^ e1 ^ " " ^ e2 ^ "\n")
  | Xor(e1, e2) ->
     print_string (indent ^ "Xor " ^ e1 ^ " " ^ e2 ^ "\n")
  | Or(e1, e2) ->
     print_string (indent ^ "Or " ^ e1 ^ " " ^ e2 ^ "\n")
  | And(e1, e2) ->
     print_string (indent ^ "And " ^ e1 ^ " " ^ e2 ^ "\n")
  | Sll(e1, e2) ->
     print_string (indent ^ "Sll " ^ e1 ^ " " ^ e2 ^ "\n")
  | Srl(e1, e2) ->
     print_string (indent ^ "Srl " ^ e1 ^ " " ^ e2 ^ "\n")
  | FNeg(e) ->
     print_string (indent ^ "FNeg " ^ e ^ "\n")
  | FAdd(e1, e2) ->
     print_string (indent ^ "FAdd " ^ e1 ^ " " ^ e2 ^ "\n")
  | FSub(e1, e2) ->
     print_string (indent ^ "FSub " ^ e1 ^ " " ^ e2 ^ "\n")
  | FMul(e1, e2) ->
     print_string (indent ^ "FMul " ^ e1 ^ " " ^ e2 ^ "\n")
  | FDiv(e1, e2) ->
     print_string (indent ^ "FDiv " ^ e1 ^ " " ^ e2 ^ "\n")
  | Sin(e1) ->
     print_string (indent ^ "Sin " ^ e1 ^ "\n")
  | Cos(e1) ->
     print_string (indent ^ "Cos " ^ e1 ^ "\n")
  | Atan(e1) ->
     print_string (indent ^ "Atan " ^ e1 ^ "\n")
  | Sqrt(e1) ->
     print_string (indent ^ "Sqrt " ^ e1 ^ "\n")
  | IfEq(e1, e2, t1, t2) ->
     print_string (indent ^ "IfEq " ^ e1 ^ " " ^ e2 ^ "\n");
     g (indent ^ "  ") t1;
     g (indent ^ "  ") t2
  | IfLE(e1, e2, t1, t2) ->
     print_string (indent ^ "IfLE " ^ e1 ^ " " ^ e2 ^ "\n");
     g (indent ^ "  ") t1;
     g (indent ^ "  ") t2
  | Let((e, t), t1, t2) ->
     print_string (indent ^ "Let " ^ e ^ "\n");
     g (indent ^ "  ") t1;
     g (indent ^ "  ") t2
  | Var(e) ->
     print_string (indent ^ "Var " ^ e ^ "\n")
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
     print_string (indent ^ "LetRec\n");
     print_string (indent ^ "  " ^ x ^ "\n");
     print_string (indent ^ "  ");
     let rec print_list = function 
       | [] -> ()
       | e::l -> print_string (e ^ " ") ; print_list l;
     in
     print_list (List.map (fun (x, t) -> x) yts);
     print_string "\n";
     g (indent ^ "  ") e1;
     g (indent ^ "  ") e2
  | App(e, es) -> (* 関数適用の型推論 (caml2html: typing_app) *)
     print_string (indent ^ "App " ^ e ^ "\n");
     print_string (indent ^ "  ");
     let rec print_list = function
       | [] -> ()
       | e::l -> print_string (e ^ " "); print_list l;
     in
     print_list es;
     print_string "\n"
  | Tuple(es) ->
     print_string (indent ^ "Tuple " ^ "\n");
     print_string (indent ^ "  ");
     let rec print_list = function
       | [] -> ()
       | e::l -> print_string (e ^ " "); print_list l;
     in
     print_list es;
     print_string "\n"
  | LetTuple(xts, e1, e2) ->
     print_string (indent ^ "LetTuple\n");
     let rec print_list = function 
       | [] -> ()
       | e::l -> print_string (e ^ " "); print_list l
     in
     print_list (List.map (fun (x, t) -> x) xts);
     print_string (indent ^ "  " ^ e1 ^ "\n");
     g (indent ^ "  ") e2
  | Get(e1, e2) ->
     print_string (indent ^ "Get " ^ e1 ^ " " ^ e2 ^ "\n")
  | Put(e1, e2, e3) ->
     print_string (indent ^ "Put " ^ e1 ^ " " ^ e2 ^ e3 ^ "\n")
  | ExtArray(e1) ->
     print_string (indent ^ "ExtArray " ^ e1 ^ "\n")
  | ExtFunApp(e, es) ->
     print_string (indent ^ "ExtFunApp " ^ e ^ "\n");
     print_string (indent ^ "  ");
     let rec print_list = function
       | [] -> ()
       | e::l -> print_string (e ^ " "); print_list l;
     in
     print_list es;
     print_string "\n"

let f e =
  g "" e;
  e
