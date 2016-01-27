open KNormal

let rec effect = function (* 副作用の有無 (caml2html: elim_effect) *)
  | Let(_, e1, e2) | If(_, _, _, e1, e2) -> effect e1 || effect e2
  | While(_, _, _, e) | LetRec(_, e) | LetTuple(_, _, e) -> effect e
  | App _ | Put _ | ExtFunApp _ | In _ | Out _ | SetHp _ | Continue _ -> true
  | _ -> false

let log = ref ""
  
let rec g = function (* 不要定義削除ルーチン本体 (caml2html: elim_f) *)
  | If(c, x, y, e1, e2) ->
     let e1, fve1 = g e1 in
     let e2, fve2 = g e2 in
     (If(c, x, y, e1, e2), (fv_if x y fve1 fve2))
  | While(x, ys, zs, e) ->
     let e, fve = g e in
     While(x, ys, zs, e), fv_while ys zs fve
  | Let((x, t), e1, e2) -> (* letの場合 (caml2html: elim_let) *)
     let e1', fve1 = g e1 in
     let e2', fve2 = g e2 in
     if effect e1' || S.mem x fve2 then (Let((x, t), e1', e2'), (fv_let x fve1 fve2)) else
       ((*log := !log ^ Format.sprintf "eliminating variable %s@." x;*)
	 (e2', fve2))
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* let recの場合 (caml2html: elim_letrec) *)
     let e1', fve1 = g e1 in
     let e2', fve2 = g e2 in
     if S.mem x fve2 then
       (LetRec({ name = (x, t); args = yts; body = e1' }, e2'), (fv_letrec x yts fve1 fve2))
     else
       ((*log := !log ^ Format.sprintf "eliminating function %s@." x;*)
	(e2', fve2))
  | LetTuple(xts, y, e) ->
      let xs = List.map fst xts in
      let e', fve = g e in
      if List.exists (fun x -> S.mem x fve) xs then (LetTuple(xts, y, e'), (fv_lettuple xts y fve)) else
	((*log := !log ^ Format.sprintf "eliminating variables %s@." (Id.pp_list xs);*)
	 (e', fve))
  | e -> (e, fv e)

let rec f e =
  log := "";
  let e, _ = g e in
  (*prerr_string !log;*)
  e
