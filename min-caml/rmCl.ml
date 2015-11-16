open KNormal

let rec g env fenv venv = function
  | IfEq(x, y, e1, e2) -> IfEq(x, y, (g env fenv venv e1), (g env fenv venv e2))
  | IfLE(x, y, e1, e2) -> IfLE(x, y, (g env fenv venv e1), (g env fenv venv e2))
  | Let((x, t), e1, e2) ->
     Let((x, t), e1, (g env fenv (M.add x t venv) e2))
  | LetRec({ name = (x, t); args = yts; body = e1}, e2) ->
     let fenv = S.add x fenv in
     let bfv = List.fold_left (fun s (y, _) -> S.remove y s) (fv e1) yts in
     if S.is_empty (S.diff bfv fenv) then
       LetRec({ name = (x, t); args = yts; body = g env fenv venv e1 }, g env fenv venv e2)
     else
       let list = S.fold (fun x l ->
	 if M.mem x venv then
	   (x, Id.genid x, M.find x venv)::l
	 else
	   l) bfv [] in
       let fn = List.fold_left (fun fn (x, _, _) -> fn ^ "_cl_" ^ x) x list in
       let yts = List.fold_left (fun yts (_, x, t) -> (x,t)::yts) yts list in
       let env = M.add x (fn, list) env in
       LetRec({ name = (fn, t); args = yts; body = g env fenv venv e1 }, g env fenv venv e2) (* let & alpha *)
  | LetTuple(xts, y, e) -> LetTuple(xts, y, (g env fenv venv e))
  | App(x, yts) when M.mem x env ->
     let fn, list = M.find x env in
     (*     let yts = List.fold_left (fun yts (x, _, t) -> (x,t)::yts) yts list in*)
     App(fn, yts)
  | e -> e
  
let rec f e =
  g M.empty S.empty M.empty e
    
