open KNormal

(* インライン展開する関数の最大サイズ (caml2html: inline_threshold) *)
let threshold = ref 50 (* Mainで-inlineオプションによりセットされる *)

let log = ref ""
  
let rec is_rec x = function
  | If(_, _, _, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | While(_, _, _, e) -> is_rec x e
  | Let(_, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | LetRec({ name = _; args = _; body = e1 }, e2) -> (is_rec x e1) || (is_rec x e2)
  | App(x', _) -> if x' = x then true else false
  | LetTuple(_, _, e) -> is_rec x e
  | e -> false


(* 非再帰関数もループ判定されてしまうので注意 *)
let rec is_loop x f = function
  | If(_, _, _, e1, e2) -> (is_loop x f e1) && (is_loop x f e2)
  | While(_, _, _, e) -> is_loop x f e
  | Let(_, e1, e2) -> (is_loop x false e1) && (is_loop x f e2)
  | LetRec(_) -> assert false
  | App(x', _) when x = x'-> f
  | LetTuple(_, _, e) -> is_loop x f e
  | e -> true

let rec has_while = function
  | If(_, _, _, e1, e2) -> (has_while e1) || (has_while e2)
  | While(_, _, _, _) -> true
  | Let(_, e1, e2) -> (has_while e1) || (has_while e2)
  | LetRec(_) -> assert false
  | LetTuple(_, _, e) -> has_while e
  | e -> false
     
let rec h' = function
  | If(_, _, _, e1, e2) ->
     (h' e1)@(h' e2)
  | While(_, _, _, e) ->
     h' e
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


(* While化ルーチン *)
let rec i f yts = function
  | If(c, x, y, e1, e2) -> If(c, x, y, i f yts e1, i f yts e2)
  | While(x, yts, zs, e) -> While(x, yts, zs, i f yts e)
  | Let(xt, e1, e2) -> Let(xt, i f yts e1, i f yts e2)
  | LetRec(_) -> assert false
  | App(x, ys) when x = f -> Continue(f, yts, ys)
  | LetTuple(xts, y, e) -> LetTuple(xts, y, i f yts e)
  | _ as e -> e
     
let rec g env fmap = function (* インライン展開ルーチン本体 (caml2html: inline_g) *)
  | If(c, x, y, e1, e2) ->
     let e1' = g env fmap e1 in
     let e2' = g env fmap e2 in
     If(c, x, y, e1', e2')
  | While(x, yts, zs, e) ->
     let e = g env fmap e in
     While(x, yts, zs, e)
  | Let((x, t), e1, e2) ->
     let e1' = g env fmap e1 in
     let e2' = g env fmap e2 in
     Let((x, t), e1', e2')
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* 関数定義の場合 (caml2html: inline_letrec) *)
(*     if is_rec x e1 && is_loop x true e1 then
       (* While展開 *)
       let e1 = While(x, yts, List.map fst yts, i x yts e1) in
       let e1 = Alpha.g M.empty e1 in
       LetRec({ name = (x, t); args = yts; body = e1 }, g env fmap e2)
     else*)
       if not (M.mem x fmap) then
         g env fmap e2
       else
         let env = M.add x (yts, e1) env in
         LetRec({ name = (x, t); args = yts; body = g env fmap e1}, g env fmap e2)
  | App(x, ys) as exp when M.mem x env -> (* 関数適用の場合 (caml2html: inline_app) *)
     let (zs, e) = M.find x env in
     if is_rec x e = false && has_while e = false (*&& ((size e) < 50 || (M.find x fmap) <= 3)*) then
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
