open KNormal

let log = ref ""
  
let find x env = try M.find x env with Not_found -> x (* 置換のための関数 (caml2html: beta_find) *)

let rec g env = function (* β簡約ルーチン本体 (caml2html: beta_g) *)
  | Unit -> Unit
  | Int(i) -> Int(i)
  | Float(d) -> Float(d)
  | Array(i) -> Array(i)
  | Neg(x) -> Neg(find x env)
  | Add(x, y) -> Add(find x env, find y env)
  | Sub(x, y) -> Sub(find x env, find y env)
  | Xor(x, y) -> Xor(find x env, find y env)
  | Or(x, y) -> Or(find x env, find y env)
  | And(x, y) -> And(find x env, find y env)
  | Sll(x, y) -> Sll(find x env, find y env)
  | Srl(x, y) -> Srl(find x env, find y env)
  | FNeg(x) -> FNeg(find x env)
  | FAdd(x, y) -> FAdd(find x env, find y env)
  | FSub(x, y) -> FSub(find x env, find y env)
  | FMul(x, y) -> FMul(find x env, find y env)
  | FDiv(x, y) -> FDiv(find x env, find y env)
  | FAM(x, y, z) -> FAM(find x env, find y env, find z env)
  | FAbs(x) -> FAbs(find x env)
  | Sqrt(x) -> Sqrt(find x env)
  | If(c, x, y, e1, e2) -> If(c, find x env, find y env, g env e1, g env e2) (* TODO *)
  | Let((x, t), e1, e2) -> (* letのβ簡約 (caml2html: beta_let) *)
      (match g env e1 with
      | Var(y) ->
	(*	 log := !log ^ Format.sprintf "beta-reducing %s = %s@." x y;*)
	g (M.add x y env) e2
      | e1' ->
	       let e2' = g env e2 in
	       Let((x, t), e1', e2'))
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
      LetRec({ name = xt; args = yts; body = g env e1 }, g env e2)
  | Var(x) -> Var(find x env) (* 変数を置換 (caml2html: beta_var) *)
  | Tuple(xs) -> Tuple(List.map (fun x -> find x env) xs)
  | LetTuple(xts, y, e) -> LetTuple(xts, find y env, g env e)
  | Get(x, y) -> Get(find x env, find y env)
  | Put(x, y, z) -> Put(find x env, find y env, find z env)
  | App(g, xs) -> App(find g env, List.map (fun x -> find x env) xs)
  | ExtArray(x) -> ExtArray(x)
  | ToFloat(x) -> ToFloat(find x env)
  | ToInt(x) -> ToInt(find x env)
  | ToArray(x) -> ToArray(find x env)
  | In(x) -> In(find x env)
  | Out(x) -> Out(find x env)
  | Count -> Count
  | ShowExec -> ShowExec
  | SetCurExec -> SetCurExec
  | GetExecDiff -> GetExecDiff
  | GetHp(x) -> GetHp(find x env)
  | SetHp(x) -> SetHp(find x env)
  | ExtFunApp(x, ys) -> ExtFunApp(x, List.map (fun y -> find y env) ys)

let f e =
  log := "";
  let e = g M.empty e in
  (*  prerr_string !log;*)
  e
