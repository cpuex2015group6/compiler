(* rename identifiers to make them unique (alpha-conversion) *)

open KNormal

let find x env = if M.mem x env then
                   M.find x env
                 else
                   x

let rec g env = function (* α変換ルーチン本体 (caml2html: alpha_g) *)
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
  | FAbA(x, y) -> FAbA(find x env, find y env)
  | FAM(x, y, z) -> FAM(find x env, find y env, find z env)
  | FAbs(x) -> FAbs(find x env)
  | Sqrt(x) -> Sqrt(find x env)
  | If(c, x, y, e1, e2) -> If(c, find x env, find y env, g env e1, g env e2)
  | While(x, yts, zs, e) ->
     let x' = Id.genid x in
     let env = M.add x x' env in
     let yts' = List.map (fun (y, t) -> (Id.genid y, t)) yts in
     let env' = List.fold_left2 (fun env (y, _) (y', _) -> M.add y y' env) env yts yts' in
     While(find x env, yts', List.map (fun z -> find z env) zs, g env' e)
  | Continue(x, yts, zs) -> Continue(find x env, List.map (fun (y, t) -> (find y env, t)) yts, List.map (fun z -> find z env) zs)
  | Let((x, t), e1, e2) -> (* letのα変換 (caml2html: alpha_let) *)
      let x' = Id.genid x in
      let e1' = g env e1 in
      Let((x', t), e1', g (M.add x x' env) e2)
  | Var(x) -> Var(find x env)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* let recのα変換 (caml2html: alpha_letrec) *)
      let env = M.add x (Id.genid x) env in
      let ys = List.map fst yts in
      let env' = M.add_list2 ys (List.map Id.genid ys) env in
      LetRec({ name = (find x env, t);
	       args = List.map (fun (y, t) -> (find y env', t)) yts;
	       body = g env' e1 },
	     g env e2)
  | App(x, ys) -> App(find x env, List.map (fun y -> find y env) ys)
  | Tuple(xs) -> Tuple(List.map (fun x -> find x env) xs)
  | LetTuple(xts, y, e) -> (* LetTupleのα変換 (caml2html: alpha_lettuple) *)
      let xs = List.map fst xts in
      let env' = M.add_list2 xs (List.map Id.genid xs) env in
      LetTuple(List.map (fun (x, t) -> (find x env', t)) xts,
	       find y env,
	       g env' e)
  | GetTuple(x, i) -> GetTuple(find x env, i)
  | Get(x, y) -> Get(find x env, find y env)
  | Put(x, y, z) -> Put(find x env, find y env, find z env)
  | ExtArray(x) -> ExtArray(x)
  | I2F(x) -> I2F(find x env)
  | F2I(x) -> F2I(find x env)
  | I2IA(x) -> I2IA(find x env)
  | I2FA(x) -> I2FA(find x env)
  | A2I(x) -> A2I(find x env)
  | In(x) -> In(find x env)
  | Out(x) -> Out(find x env)
  | GetHp(x) -> GetHp(find x env)
  | SetHp(x) -> SetHp(find x env)
  | ExtFunApp(x, ys) -> ExtFunApp(x, List.map (fun y -> find y env) ys)

let f = g M.empty
