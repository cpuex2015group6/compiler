open KNormal

let toplevel : fundef list ref = ref []
  
let rec g env = function
  | IfEq(x, y, e1, e2) -> IfEq(x, y, (g env e1), (g env e2))
  | IfLE(x, y, e1, e2) -> IfLE(x, y, (g env e1), (g env e2))
  | Let(xt, e1, e2) -> Let(xt, e1, (g env e2))
  | LetRec({ name = (x, t); args = yts; body = e1}, e2) as exp ->
     let env = S.add x env in
     let bfv = List.fold_left (fun s (y, _) -> S.remove y s) (fv e1) yts in
     if S.is_empty (S.diff bfv env)  then
       let toplevel2 = !toplevel in
       toplevel := [];
       let e1 = g env e1 in
       toplevel := { name = (x, t); args = yts; body = e1 } :: !toplevel @ toplevel2;
       (g env e2)
     else
       (prerr_endline (x^" fuck");
       S.iter (fun x -> prerr_endline x) (List.fold_left (fun s (y, _) -> S.remove y s) (fv e1) yts);
       LetRec({ name = (x, t); args = yts; body = e1 }, g env e2))
  | LetTuple(xts, y , e) -> LetTuple(xts, y, (g env e))
  | e -> e
     
     
let rec f e =
  toplevel := [];
  let e = g S.empty e in
  let e = List.fold_left
    (fun e fundef ->
      LetRec(fundef, e))
    e
    !toplevel
  in
  KNormaledAst.f e;
    e
