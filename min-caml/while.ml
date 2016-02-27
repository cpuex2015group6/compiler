open KNormal
(* ループ関連の最適化 *)
(*
let union m1 m2 = M.fold (fun k v m -> M.add k v m) m1 m2
  
let rec g destt env = function
  | If(c, x, y, e1, e2) ->
     let fl1, e1 = g destt env e1 in
     let fl2, e2 = g destt env e2 in
     union fl1 fl2, If(c, x, y, e1, e2)
  | While(x, yts, zs, e) as exp ->
     let x' = Id.genid x in
     let fvs = fv exp in
     let fvs = List.fold_left (fun fvs z -> S.remove z fvs) fvs zs in
     let fvs = S.fold (fun fv fvs -> try ((fv, M.find fv env)::fvs) with Not_found -> fvs) fvs [] in
     let fyts = (List.fold_left2 (fun zs z (_, t) -> zs@[(z, t)]) [] zs yts) @ fvs in
     M.add x' (Type.Fun(List.map snd fyts, destt), fyts, (While(x, yts, zs, e))) M.empty, App(x', List.map fst fyts)
  | Let((x, t) as xt, e1, e2) ->
     let fl1, e1 = g t env e1 in
     let fl2, e2 = g destt (M.add x t env) e2 in
     union fl1 fl2, Let(xt, e1, e2)
  | LetRec(_) -> assert false
  | LetTuple(xts, y, e) ->
     let fl, e = g destt (List.fold_left (fun env (x, t) -> M.add x t env) env xts) e in
     fl, LetTuple(xts, y, e)
  | e -> M.empty, e
       
  
let rec f = function
  | If(c, x, y, e1, e2) -> If(c, x, y, f e1, f e2)
  | While(x, yts, zs, e) -> While(x, yts, zs, f e)
  | Let(xt, e1, e2) -> Let(xt, f e1, f e2)
  | LetRec({ name = _; args = _; body = While(_)} as fundef, e2) -> LetRec(fundef, f e2)
  | LetRec({ name = (x, t) as xt; args = yts; body = e1 } as fundef, e2) ->
     let rec f' env = function
       | Let((x, _), _, e2) ->
          f' (S.add x env) e2
       | While(_, _, zs, _) ->
          S.for_all (fun v -> List.mem v zs) env
       | _ ->
          false
     in
     if not (has_while e1) ||  f' S.empty e1 then
       LetRec(fundef, f e2)
     else
       let fl, e1 = g t (List.fold_left (fun env (y, t) -> M.add y t env) M.empty yts) e1 in
       M.fold
         (fun x (t, yts, body) e -> LetRec({ name = (x, t); args = yts; body = body }, e))
         fl
         (LetRec({ name = xt; args = yts; body = e1 }, f e2))
  | LetTuple(xts, y, e) -> LetTuple(xts, y, f e)
  | e -> e
*)


let rec f e = e
  
