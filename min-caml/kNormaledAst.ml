(* print kNormaledAST K正規化後のASTを表示する *)

open KNormal

let rec print_type = function
    | Type.Unit ->
       print_string "Unit"
    | Type.Bool ->
       print_string "Bool"
    | Type.Int ->
       print_string "Int"
    | Type.Float ->
       print_string "Float"
    | Type.Fun(ts, t) ->
       let rec print_args = function
         | [] -> ()
         | t::ts -> print_type t;
                    print_string "->";
                    print_args ts
       in
       print_string "Fun(";
       print_args ts;
       print_type t;
       print_string ")"
    | Type.Tuple(ts) ->
       let rec print_list = function
              | t::[] -> print_type t
              | t::ts -> print_type t;
                         print_string " ";
                         print_list ts
              | [] -> ()
       in
       print_string "Tuple(";
       print_list ts;
       print_string ")"
    | Type.Array(t) ->
       print_string "Array(";
       print_type t;
       print_string ")"
    | Type.Var(t) ->
       print_string "Var(";
       (match !t with
        | None ->
           print_string "None"
        | Some(t) ->
           print_type t);
       print_string ")"


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
  | Array(v) ->
     print_string (indent ^ "Array ");
     print_int v;
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
  | FAbA(e1, e2) ->
     print_string (indent ^ "FAbA " ^ e1 ^ " " ^ e2 ^ "\n")
  | FAM(e1, e2, e3) ->
     print_string (indent ^ "FAM " ^ e1 ^ " " ^ e2 ^ " " ^ e3 ^ "\n")
  | FAbs(e1) ->
     print_string (indent ^ "FAbs " ^ e1 ^ "\n")
  | Sqrt(e1) ->
     print_string (indent ^ "Sqrt " ^ e1 ^ "\n")
  | If(c, e1, e2, t1, t2) ->
     Printf.printf "%sIf %d %s %s\n" indent c e1 e2;
    print_string (indent ^ "{\n");
    g (indent ^ "  ") t1;
    print_string (indent ^ "} Else {" ^ "\n");
    g (indent ^ "  ") t2;
    print_string (indent ^ "}\n")
  | While(x, yts, zs, e) ->
     Printf.printf "%sWhile %s\n" indent x;
    print_string (indent ^ "  vars:");
    let rec print_list = function
      | [] -> ()
      | e::l -> print_string (e ^ " "); print_list l;
    in
    print_list (List.map fst yts);
    print_string "\n";
    print_string (indent ^ "  init:");
    print_list zs;
    print_string "\n";
    print_string (indent ^ "{\n");
    g (indent ^ "  ") e;
    print_string (indent ^ "}\n")
  | Continue(x, yts, zs) ->
     Printf.printf "%sContinue %s\n" indent x;
    let rec print_list = function
      | [] -> ()
      | e::l -> print_string (e ^ " "); print_list l;
    in
    print_string (indent ^ "  vars:");
    print_list (List.map fst yts);
    print_string "\n";
    print_string (indent ^ "  zs:");
    print_list zs;
    print_string "\n";
  | Let((e, t), t1, t2) ->
     print_string (indent ^ "Let " ^ e ^ " ");
     print_type t;
     print_string "\n";
     g (indent ^ "  ") t1;
     g indent t2
  | Var(e) ->
     print_string (indent ^ "Var " ^ e ^ "\n")
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
     print_string (indent ^ "LetRec\n");
     print_string (indent ^ "  " ^ x ^ " ");
     print_type t;
     print_string "\n";
     print_string (indent ^ "  ");
     let rec print_list = function 
       | [] -> ()
       | e::l -> print_string (e ^ " ") ; print_list l;
     in
     print_list (List.map fst yts);
     print_string "\n";
     print_string (indent ^ "{\n");
     g (indent ^ "  ") e1;
     print_string (indent ^ "}\n");
     g indent e2
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
     print_string (indent ^ "  ");
     print_list (List.map (fun (x, t) -> x) xts);
     print_string (indent ^ "  " ^ e1 ^ "\n");
     g indent e2
  | GetTuple(e, i) ->
     Format.printf "%sGetTuple %s %d\n" indent e i
  | Get(e1, e2) ->
     print_string (indent ^ "Get " ^ e1 ^ " " ^ e2 ^ "\n")
  | Put(e1, e2, e3) ->
     print_string (indent ^ "Put " ^ e1 ^ " " ^ e2 ^ " " ^ e3 ^ "\n")
  | ExtArray(e1) ->
     print_string (indent ^ "ExtArray " ^ e1 ^ "\n")
  | I2F(e1) ->
     print_string (indent ^ "I2F " ^ e1 ^ "\n")
  | F2I(e1) ->
     print_string (indent ^ "F2I " ^ e1 ^ "\n")
  | I2IA(e1) ->
     print_string (indent ^ "I2IA " ^ e1 ^ "\n")
  | I2FA(e1) ->
     print_string (indent ^ "I2FA " ^ e1 ^ "\n")
  | A2I(e1) ->
     print_string (indent ^ "A2I " ^ e1 ^ "\n")
  | In(e1) ->
     print_string (indent ^ "In " ^ e1 ^ "\n")
  | Out(e1) ->
     print_string (indent ^ "Out " ^ e1 ^ "\n")
  | GetHp(e1) ->
     print_string (indent ^ "GetHp " ^ e1 ^ "\n")
  | SetHp(e1) ->
     print_string (indent ^ "SetHp " ^ e1 ^ "\n")
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
  print_endline "";
  e
