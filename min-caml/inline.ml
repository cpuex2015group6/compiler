open KNormal

(* ����饤��Ÿ������ؿ��κ��祵���� (caml2html: inline_threshold) *)
let threshold = ref 50 (* Main��-inline���ץ����ˤ�ꥻ�åȤ���� *)

let rec is_rec x = function
  | If(_, _, _, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | While(_, _, _, e) -> is_rec x e
  | Let(_, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | LetRec({ name = _; args = _; body = e1 }, e2) -> (is_rec x e1) || (is_rec x e2)
  | App(x', _) -> if x' = x then true else false
  | LetTuple(_, _, e) -> is_rec x e
  | e -> false


(* ��Ƶ��ؿ���롼��Ƚ�ꤵ��Ƥ��ޤ��Τ���� *)
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

(* �ؿ����Ȳ��������� *)
let h e =
  List.fold_left (fun m x -> try M.add x (1 + (M.find x m)) m with Not_found -> M.add x 1 m) M.empty (h' e)

let rec apply f = function
  | If(c, x, y, e1, e2) -> f (If(c, x, y, apply f e1, apply f e2))
  | While(x, yts, zs, e) -> f (While(x, yts, zs, apply f e))
  | Let(xt, e1, e2) -> f (Let(xt, apply f e1, apply f e2))
  | LetRec(_) -> assert false
  | LetTuple(xts, y, e) -> f (LetTuple(xts, y, apply f e))
  | e -> f e

let rec g env fmap = function (* ����饤��Ÿ���롼�������� (caml2html: inline_g) *)
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
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* �ؿ�����ξ�� (caml2html: inline_letrec) *)
     if is_rec x e1 && is_loop x true e1 then
       (* WhileŸ�� *)
       let we = apply (fun e -> match e with | App(f, ys) when x = f -> Continue(f, yts, ys) | _ -> e) e1 in
       let e1 = apply (fun e -> match e with | App(f, ys) when x = f -> While(x, yts, ys, we) | _ -> e) e1 in
       let e1 = Alpha.g M.empty e1 in
       let e1 = g env fmap e1 in
       LetRec({ name = (x, t); args = yts; body = e1 }, g env fmap e2)
     else
       if not (M.mem x fmap) then
         g env fmap e2
       else
         let env = M.add x (yts, e1) env in
         LetRec({ name = (x, t); args = yts; body = g env fmap e1}, g env fmap e2)
  | App(x, ys) as exp when M.mem x env -> (* �ؿ�Ŭ�Ѥξ�� (caml2html: inline_app) *)
     let (zs, e) = M.find x env in
     if is_rec x e = false && ((M.find x fmap) <= 1 || has_while e = false) then
       ((*prerr_endline ("inlining " ^ x ^ ".");*)
	       let env' =
	         List.fold_left2
  	         (fun env' (z, t) y -> M.add z y env')
	           M.empty
	           zs
	           ys in
	       let e = Alpha.g env' e in
         g env fmap e
       )
     else
       exp
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env fmap e)
  | e -> e

let f e =
  let e = g M.empty (h e) e in
  e
