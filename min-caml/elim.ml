open KNormal

let rec effect = function (* �����Ѥ�̵ͭ (caml2html: elim_effect) *)
  | Let(_, e1, e2) | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) -> effect e1 || effect e2
  | LetRec(_, e) | LetTuple(_, _, e) -> effect e
  | App _ | Put _ | ExtFunApp _ | In _ | Out _ | Count | ShowExec | SetCurExec | GetExecDiff | SetHp _-> true
  | _ -> false

let log = ref ""
  
let rec g = function (* �����������롼�������� (caml2html: elim_f) *)
  | IfEq(x, y, e1, e2) ->
     let e1, fve1 = g e1
     in
     let e2, fve2 = g e2
     in
     (IfEq(x, y, e1, e2), (fv_if x y fve1 fve2))
  | IfLE(x, y, e1, e2) ->
     let e1, fve1 = g e1
     in
     let e2, fve2 = g e2
     in
     (IfLE(x, y, e1, e2), (fv_if x y fve1 fve2))
  | Let((x, t), e1, e2) -> (* let�ξ�� (caml2html: elim_let) *)
     let e1', fve1 = g e1 in
     let e2', fve2 = g e2 in
     if effect e1' || S.mem x fve2 then (Let((x, t), e1', e2'), (fv_let x fve1 fve2)) else
       ((*log := !log ^ Format.sprintf "eliminating variable %s@." x;*)
	 (e2', fve2))
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* let rec�ξ�� (caml2html: elim_letrec) *)
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
