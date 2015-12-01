(* flatten let-bindings (just for prettier printing) *)

open KNormal

let rec f = function (* �ͥ��Ȥ���let�δ����tuple��Ÿ�� (caml2html: assoc_f) *)
  | If(x, e1, e2) -> If(x, f e1, f e2)
  | Let(xt, e1, e2) -> (* let�ξ�� (caml2html: assoc_let) *)
     let rec insert = function
	     | Let(yt, e3, e4) -> Let(yt, e3, insert e4)
	     | LetRec(fundefs, e) -> LetRec(fundefs, insert e)
	     | LetTuple(yts, z, e) -> LetTuple(yts, z, insert e)
	     | e -> Let(xt, e, f e2) in
     insert (f e1)
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
     LetRec({ name = xt; args = yts; body = f e1 }, f e2)
  | LetTuple(xts, y, e) ->
     let e, _ = List.fold_left (fun (e, offset) xt -> (Let(xt, GetTuple(y, offset), e), offset + 1)) ((f e), 0) xts
     in
     e
  | e -> e
