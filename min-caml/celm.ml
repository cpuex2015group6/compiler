(* common subexpression elimination 共通部分式削除を行う *)

open KNormal

let rec i venv env = function
  | If(c, x, y, e1, e2) ->
     let e1, env1 = i venv env e1 in
     let e2, env2 = i venv env e2 in
     let env = M.fold (fun k d m -> if (M.mem k env1) && (M.mem k env2) then M.add k d m else m) env M.empty
     in
     If(c, x, y, e1, e2), env
  | While(x, ys, zs, e) ->
     let e, env = i venv env e in
     While(x, ys, zs, e), env
  | Let((x, t), (Get(a, ix)), e2) when M.mem ix venv ->
     let av = Format.sprintf "%s_i%d" a (M.find ix venv) in
     (
       try
	       (
	         let v = M.find av env in
	         let e2, env = i venv env e2 in
	         Let((x, t), Var(v), e2), env 
	       ) with Not_found ->
	         let e2, env = i venv (M.add av x env) e2 in
	         Let((x, t), (Get(a, ix)), e2), env
     )
  | Let((x, t), (GetTuple(a, ix)), e2) ->
     let av = Format.sprintf "%s_i%d" a ix in
     (
       try
	 (
	   let v = M.find av env in
	   let e2, env = i venv env e2 in
	   Let((x, t), Var(v), e2), env 
	 ) with Not_found ->
	   let e2, env = i venv (M.add av x env) e2 in
	   Let((x, t), (GetTuple(a, ix)), e2), env
     )
  | Let((x, t), (Int(imm)), e2) ->
     let e2, env = i (M.add x imm venv) env e2 in
     Let((x, t), (Int(imm)), e2), env
  | Let((x, t), e1, e2) ->
     let e1, env = i venv env e1 in
     let e2, env = i venv env e2 in
     Let((x, t), e1, e2), env
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
     let e1, _ = i venv M.empty e1 in
     let e2, env = i venv env e2 in
     LetRec({ name = xt; args = yts; body = e1 }, e2), env
  | LetTuple(xts, e1, e2) ->
     let e2, env = i venv env e2 in
     LetTuple(xts, e1, e2), env
  | App(_) as e ->
     e, M.empty
  | Put(_) as e ->
     e, M.empty
  | e ->
     e, env

let h e =
  let e, _ = i M.empty M.empty e in
  e
  
let rec search history e =
  match history with
    | [] -> e
    | (v, e1)::xs ->
       match e1 with
         | App(_)
         | ExtFunApp(_)
         | In(_)
         | Out(_)
         | GetHp(_)
         | SetHp(_)
         | Get (_)
         | Put(_) ->
            e
         | _  when e1 = e ->
            Var(v)
         | _ ->
            search xs e
	      
let rec g history = function
  | If(c, x, y, t1, t2) ->
     let nt1 = g history t1 in
     let nt2 = g history t2 in
     If(c, x, y, nt1, nt2)
  | Let((e, t), t1, t2) ->
     let nt1 = g history t1 in
     let nt2 = g ((e,nt1)::history) t2 in
     Let((e, t), nt1, nt2)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
     let ne1 = g history e1 in
     let ne2 = g history e2 in
     LetRec({ name = (x, t); args = yts; body = ne1 }, ne2)
  | LetTuple(xts, e1, e2) ->
     (* 手抜き　本当はxtsもhistoryに追加すべき *)
     let ne2 = g history e2 in
     LetTuple(xts, e1, ne2)
  | e ->
     search history e

let f e = g [] e
