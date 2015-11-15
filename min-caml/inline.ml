open KNormal

(* インライン展開する関数の最大サイズ (caml2html: inline_threshold) *)
let threshold = ref 50 (* Mainで-inlineオプションによりセットされる *)

let log = ref ""
  
let rec size = function
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2)
  | Let(_, e1, e2) | LetRec({ body = e1 }, e2) -> 1 + size e1 + size e2
  | LetTuple(_, _, e) -> 1 + size e
  | _ -> 1

let rec is_rec x = function
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | Let(_, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | LetRec({ name = _; args = _; body = e1 }, e2) -> (is_rec x e1) || (is_rec x e2)
  | App(x', _) -> if x' = x then true else false
  | LetTuple(_, _, e) -> is_rec x e
  | e -> false

let rec g env cenv = function (* インライン展開ルーチン本体 (caml2html: inline_g) *)
  | IfEq(x, y, e1, e2) ->
     let e1' = g env cenv e1 in
     let e2' = g env cenv e2 in
     IfEq(x, y, e1', e2')
  | IfLE(x, y, e1, e2) ->
     let e1' = g env cenv e1 in
     let e2' = g env cenv e2 in
     IfLE(x, y, e1', e2')
  | Let((x, t), e1, e2) ->
     let e1' = g env cenv e1 in
     let cenv =
       match e1' with
       | Int(_) | Float(_) -> M.add x e1' cenv
       | _ -> cenv
     in
     let e2' = g env cenv e2 in
     Let((x, t), e1', e2')
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* 関数定義の場合 (caml2html: inline_letrec) *)
     let env = M.add x (size e1, yts, e1) env in
     LetRec({ name = (x, t); args = yts; body = g env cenv e1}, g env cenv e2)
  | App(x, ys) as exp when M.mem x env -> (* 関数適用の場合 (caml2html: inline_app) *)
     let (size, zs, e) = M.find x env in
     (* サイズと出現回数で制限を掛ける *)
     if is_rec x e = false then
       (log := !log ^ (Format.sprintf "inlining %s@." x);
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

let f e =
  log := "";
  prerr_endline "start inlining...";
  let e = g M.empty M.empty e in
  prerr_string !log;
  e
