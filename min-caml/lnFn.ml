open KNormal

let toplevel : fundef list option ref  = ref (Some [])
  
let rec g env = function
  | IfEq(x, y, e1, e2) -> IfEq(x, y, (g env e1), (g env e2))
  | IfLE(x, y, e1, e2) -> IfLE(x, y, (g env e1), (g env e2))
  | Let(xt, e1, e2) -> Let(xt, e1, (g env e2))
  | LetRec({ name = (x, t); args = yts; body = e1}, e2) as exp when !toplevel <> None->
     let env = S.add x env in
     let bfv = List.fold_left (fun s (y, _) -> S.remove y s) (fv e1) yts in
     if S.is_empty (S.diff bfv env) then
       let e1 = g env e1 in
       match !toplevel with
       | None -> assert false
       | Some(l) ->
	  toplevel := Some ({ name = (x, t); args = yts; body = e1 } :: l);
	 (g env e2)
     else
       ((*assert false;*)
       LetRec({ name = (x, t); args = yts; body = e1 }, g env e2))
  | LetRec({ name = (x, t); args = yts; body = e1}, e2) as exp ->
     let env = S.add x env in 
     toplevel := Some [];
     let e1 = g env e1 in
     let toplevel2 = !toplevel in
     toplevel := None;
     let e2 = g env e2 in
     let e = match toplevel2 with
       | None -> assert false
       | Some(l:fundef list) -> 
	  List.fold_left
	    (fun e1 fundef ->
	      LetRec(fundef, e1))
	    (LetRec({ name = (x, t); args = yts; body = e1 }, e2))
	    l
     in
     e
  | LetTuple(xts, y , e) -> LetTuple(xts, y, (g env e))
  | e -> e
     
     
let rec f e =
  toplevel := None;
  g S.empty e
