open KNormal

(* インライン展開する関数の最大サイズ (caml2html: inline_threshold) *)
let threshold = ref 50 (* Mainで-inlineオプションによりセットされる *)

let log = ref ""
  
let rec is_rec x = function
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | Let(_, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | LetRec({ name = _; args = _; body = e1 }, e2) -> (is_rec x e1) || (is_rec x e2)
  | App(x', _) -> if x' = x then true else false
  | LetTuple(_, _, e) -> is_rec x e
  | e -> false

(* 関数参照回数カウント *)
let rec h e =
  let merge m1 m2 =
    M.fold (fun k v m -> if M.mem k m then m else M.add k v m)
    m2 (M.fold (fun k v m -> try M.add k ((M.find k m2) + v) m with Not_found -> M.add k v m) m1 M.empty)
  in
  match e with
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) ->
     merge (h e1) (h e2)
  | Let(_, e1, e2) ->
     merge (h e1) (h e2)
  | LetRec({ name = _; args = _; body = e1 }, e2) ->
     merge (h e1) (h e2)
  | App(x, _) ->
     M.singleton x 1
  | LetTuple(_, _, e) ->
     h e
  | _ -> M.empty
       
     
let rec g env cenv fmap = function (* インライン展開ルーチン本体 (caml2html: inline_g) *)
  | IfEq(x, y, e1, e2) ->
     let e1' = g env cenv fmap e1 in
     let e2' = g env cenv fmap e2 in
     IfEq(x, y, e1', e2')
  | IfLE(x, y, e1, e2) ->
     let e1' = g env cenv fmap e1 in
     let e2' = g env cenv fmap e2 in
     IfLE(x, y, e1', e2')
  | Let((x, t), e1, e2) ->
     let e1' = g env cenv fmap e1 in
     let cenv =
       match e1' with
       | Int(_) | Float(_) -> M.add x e1' cenv
       | _ -> cenv
     in
     let e2' = g env cenv fmap e2 in
     Let((x, t), e1', e2')
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* 関数定義の場合 (caml2html: inline_letrec) *)
     if not (M.mem x fmap) then
       g env cenv fmap e2
     else
       let env = M.add x (yts, e1) env in
       LetRec({ name = (x, t); args = yts; body = g env cenv fmap e1}, g env cenv fmap e2)
  | App(x, ys) as exp when M.mem x env -> (* 関数適用の場合 (caml2html: inline_app) *)
     let (zs, e) = M.find x env in
     if is_rec x e = false && ((size e) < 30 || (M.find x fmap) = 1) then
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
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env cenv fmap e)
  | e -> e

let f e =
  log := "";
  let e = g M.empty M.empty (h e) e in
  prerr_string !log;
  e
