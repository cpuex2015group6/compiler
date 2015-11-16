open KNormal

let rec g env fenv  = function
  | IfEq(x, y, e1, e2) -> IfEq(x, y, (g env fenv e1), (g env fenv e2))
  | IfLE(x, y, e1, e2) -> IfLE(x, y, (g env fenv e1), (g env fenv e2))
  | Let(xt, e1, e2) -> Let(xt, e1, (g env fenv e2))
  | LetRec({ name = (x, t); args = yts; body = e1}, e2) ->
     let fenv = S.add x fenv in
     let bfv = List.fold_left (fun s (y, _) -> S.remove y s) (fv e1) yts in
     if S.is_empty (S.diff bfv fenv) then
       LetRec({ name = (x, t); args = yts; body = g env fenv e1 }, g env fenv e2)
     else
       let x = (x^"_nc") in
       let yts = yts in
       let env = M.add x [] env in
       LetRec({ name = (x, t); args = yts; body = g env fenv e1 }, g env fenv e2)
  | LetTuple(xts, y , e) -> LetTuple(xts, y, (g env fenv e))
  | App(x, ys) when M.mem x env ->
     App(x, ys)
  | e -> e
  
let rec f e =
  g M.empty S.empty e
    
