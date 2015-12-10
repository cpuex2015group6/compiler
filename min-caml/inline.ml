open KNormal

(* インライン展開する関数の最大サイズ (caml2html: inline_threshold) *)
let threshold = ref 50 (* Mainで-inlineオプションによりセットされる *)

let log = ref ""
  
let rec is_rec x = function
  | If(_, _, _, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | Let(_, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | LetRec({ name = _; args = _; body = e1 }, e2) -> (is_rec x e1) || (is_rec x e2)
  | App(x', _) -> if x' = x then true else false
  | LetTuple(_, _, e) -> is_rec x e
  | e -> false

let rec h' e =
  match e with
  | If(_, _, _, e1, e2) ->
     (h' e1)@(h' e2)
  | Let(_, e1, e2) ->
     (h' e1)@(h' e2)
  | LetRec({ name = _; args = _; body = e1 }, e2) ->
     (h' e1)@(h' e2)
  | App(x, _) ->
     [x]
  | LetTuple(_, _, e) ->
     h' e
  | _ -> []

(* 関数参照回数カウント *)
let h e =
  List.fold_left (fun m x -> try M.add x (1 + (M.find x m)) m with Not_found -> M.add x 1 m) M.empty (h' e)

     
let rec g env fmap = function (* インライン展開ルーチン本体 (caml2html: inline_g) *)
  | If(c, x, y, e1, e2) ->
     let e1' = g env fmap e1 in
     let e2' = g env fmap e2 in
     If(c, x, y, e1', e2')
  | Let((x, t), e1, e2) ->
     let e1' = g env fmap e1 in
     let e2' = g env fmap e2 in
     Let((x, t), e1', e2')
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* 関数定義の場合 (caml2html: inline_letrec) *)
     if not (M.mem x fmap) then
       g env fmap e2
     else
       let env = M.add x (yts, e1) env in
       LetRec({ name = (x, t); args = yts; body = g env fmap e1}, g env fmap e2)
  | App(x, ys) as exp when M.mem x env -> (* 関数適用の場合 (caml2html: inline_app) *)
     let (zs, e) = M.find x env in
     if is_rec x e = false (*&& ((size e) < 50 || (M.find x fmap) <= 3)*) then
       ((*log := !log ^ (Format.sprintf "inlining %s@." x);*)
	let env' =
	  List.fold_left2
  	    (fun env' (z, t) y -> M.add z y env')
	    M.empty
	    zs
	    ys in
	Alpha.g env' e)
       else
       exp
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env fmap e)
  | e -> e

let f e =
  log := "";
  let e = g M.empty (h e) e in
  (*  prerr_string !log;*)
  e
