open KNormal

(* インライン展開する関数の最大サイズ (caml2html: inline_threshold) *)
let threshold = ref 30 (* Mainで-inlineオプションによりセットされる *)

let rec size = function
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2)
  | Let(_, e1, e2) | LetRec({ body = e1 }, e2) -> 1 + size e1 + size e2
  | LetTuple(_, _, e) -> 1 + size e
  | _ -> 1

let memi x env =
  try (match M.find x env with Int(_) -> true | _ -> false)
  with Not_found -> false
let memf x env =
  try (match M.find x env with Float(_) -> true | _ -> false)
  with Not_found -> false
let memt x env =
  try (match M.find x env with Tuple(_) -> true | _ -> false)
  with Not_found -> false

let rec is_rec x = function
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | Let(_, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | LetRec({ name = _; args = _; body = e1 }, e2) -> (is_rec x e1) || (is_rec x e2)
  | App(x', _) -> if x' = x then true else false
  | LetTuple(_, _, e) -> is_rec x e
  | e -> false
    
let rec g env cenv = function (* インライン展開ルーチン本体 (caml2html: inline_g) *)
  | IfEq(x, y, e1, e2) -> IfEq(x, y, g env cenv e1, g env cenv e2)
  | IfLE(x, y, e1, e2) ->
     IfLE(x, y, g env cenv e1, g env cenv e2)
  | Let((x, t), e1, e2) ->
     let e1' = g env cenv e1 in
     let cenv =
       match e1' with
       | Int(_) | Float(_) -> S.add x cenv
       | _ -> cenv
     in
     let e2' = g env cenv e2 in
     Let((x, t), e1', e2')
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* 関数定義の場合 (caml2html: inline_letrec) *)
     let env = M.add x (size e1, yts, e1) env in
     LetRec({ name = (x, t); args = yts; body = g env cenv e1}, g env cenv e2)
  | App(x, ys) as exp when M.mem x env -> (* 関数適用の場合 (caml2html: inline_app) *)
     let (size, zs, e) = M.find x env in 
     let rec hasconst = function
       | [] -> false
       | y::ls -> (S.mem y cenv) || (hasconst ls)
     in
     if (size < !threshold) || (is_rec x e = false) then
       (Format.eprintf "inlining %s@." x;
	let env' =
	  List.fold_left2
  	    (fun env' (z, t) y -> M.add z y env')
	    M.empty
	    zs
	    ys in
	Alpha.g env' e)
     else
       exp
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env cenv e)
  | e -> e

let f e = g M.empty S.empty e
