(* アルティメットまどか *)

open KNormal

let rec g env fenv venv = function
  | IfEq(x, y, e1, e2) ->
     let e1 = g env fenv venv e1 in
     IfEq(x, y, e1, (g env fenv venv e2))
  | IfLE(x, y, e1, e2) ->
     let e1 = g env fenv venv e1 in
     IfLE(x, y, e1, (g env fenv venv e2))
  | Let((x, t), e1, e2) ->
     let e1 = g env fenv venv e1 in
     Let((x, t), e1, (g env fenv (M.add x t venv) e2))
  | LetRec({ name = (x, t); args = yts; body = e1}, e2) as exp ->
     let bfv = S.diff (S.union fenv (fv_func x yts (fv e1))) fenv in
     let venv = List.fold_left (fun venv (x, t) -> M.add x t venv) venv yts  in
     if S.is_empty bfv then
       let fenv = S.add x fenv in
       let e1 = g env fenv venv e1 in
       LetRec({ name = (x, t); args = yts; body = e1 }, g env fenv venv e2)
     else
       let list = S.fold (fun x l ->
	 if M.mem x venv then
	   (x, Id.genid x, M.find x venv)::l
	 else
	   l) bfv [] in
       let fn = List.fold_left (fun fn (x, _, _) -> fn ^ "_fv_" ^ x) x list in
       let fenv = S.add x (S.add fn fenv) in
       let yts = List.fold_left (fun yts (_, x, t) -> (x,t)::yts) yts list in
       let env = M.add x (fn, list) env in
       let env' = List.fold_left (fun env' (x, x', _) -> M.add x x' env') M.empty list in
       Format.eprintf "delete free variable(s) %s from %s and generate %s@." (Id.pp_list (List.rev_map (fun (x, _, _) -> x) list)) x fn;
       let body = Alpha.g env' (g env fenv venv e1) in
       (match t with
       | Type.Fun(ats,rt) ->
	  let ats = List.fold_left (fun ats (_, _, t) -> t::ats) ats list in
	  LetRec({ name = (fn, Type.Fun(ats, rt)); args = yts; body = body }, g env fenv venv e2)
       | _ -> assert false)
  | LetTuple(xts, y, e) -> LetTuple(xts, y, (g env fenv venv e))
  | App(x, yts) when M.mem x env ->
     let fn, list = M.find x env in
     let yts = List.fold_left (fun yts (x, _, _) -> x::yts) yts list in
     App(fn, yts)
  | e -> e
  
let rec f e =
  prerr_endline "removing free variables...";
  let rec iter e =
    let e' = g M.empty S.empty M.empty e in
    if e = e' then
      e'
    else
      iter e'
  in
  let e = iter e in
  prerr_endline "removing free variables end";
  e
    
