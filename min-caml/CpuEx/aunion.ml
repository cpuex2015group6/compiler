(* 最適化パターンの登録と実行 *)

open Asm

exception Unmatched

let rec check env x f c = try (
  match M.find x env with
  | Ans(Mr(x)) -> check env x f c
  | Ans(e) -> f e
  | _ -> raise Unmatched
) with | Unmatched | Not_found -> c ()
let fail = (fun _ -> raise Unmatched)

let rec check_ans f  = function
  | Ans(exp) -> check_ans_exp f exp
  | Let(_, _, e) -> check_ans f e
and check_ans_exp f = function
  | If(_, _, _, e1, e2) | FIf(_, _, _, e1, e2) -> check_ans f e1 && check_ans f e2
  | IfThen(_, e, _) -> check_ans f e && check_ans_exp f (Li(C(0)))
  | exp -> f exp
    
      
  
let pat = [
  (fun env -> function
  | FAbs(x) ->
     check env x (fun e -> match e with
     | FAdd(y, z) -> Ans(FAbA(y, z))
     | _ -> raise Unmatched) fail
  | _ -> raise Unmatched);
  (fun env -> function
  | If(c, x, y, Ans(Li(C(1))), Ans(Li(C(0)))) -> Ans(Cmp(c, x, V(y)))
  | _ -> raise Unmatched);
  (fun env -> function
  | If(c, x, y, Ans(Li(C(0))), Ans(Li(C(1)))) -> Ans(Cmp(Asm.negcond c, x, V(y)))
  | _ -> raise Unmatched);
  (fun env -> function
  | FIf(c, x, y, Ans(Li(C(1))), Ans(Li(C(0)))) -> Ans(FCmp(c, x, y))
  | _ -> raise Unmatched);
  (fun env -> function
  | FIf(c, x, y, Ans(Li(C(0))), Ans(Li(C(1)))) -> Ans(FCmp(Asm.negcond c, x, y))
  | _ -> raise Unmatched);
  (fun env -> function
  | IfThen(f, Ans(Cmp(c, x, y)), t) ->
     assert (List.length t = 0);
    let t1 = Id.genid "t" in
    Let([(t1, Type.Int)], Mr(f), Ans(Cmpa(c, x, y, t1)));
  | _ -> raise Unmatched);
  (fun env -> function
  | IfThen(f, Ans(FCmp(c, x, y)), t) ->
     assert (List.length t = 0); 
     let t1 = Id.genid "t" in
     Let([(t1, Type.Int)], Mr(f), Ans(FCmpa(c, x, y, t1)));
  | _ -> raise Unmatched);
  (fun env -> function
  | If(c, x, y, e, Ans(Li(C(0)))) ->
     let t1 = Id.genid "t" in
     Let([(t1, Type.Int)], Cmp(c, x, V(y)), Ans(IfThen(t1, e, [])));
  | _ -> raise Unmatched);
  (fun env -> function
  | FIf(c, x, y, e, Ans(Li(C(0)))) ->
     let t1 = Id.genid "t" in
     Let([(t1, Type.Int)], FCmp(c, x, y), Ans(IfThen(t1, e, [])));
    | _ -> raise Unmatched);
]

let h env e = 
  match List.fold_left (fun a p ->
    match a with
    | Some (Ans(e)) -> (try Some (p env e) with Unmatched -> Some (Ans(e)))
    | Some _ -> a
    | None -> (try Some (p env e) with Unmatched -> None)) None pat with
  | Some x -> x
  | None -> Ans(e)
  
let rec g env = function
  | Ans(e) -> g' env e
  | Let(xts, e1, e2) ->
     (match xts with
     | [(x, t)] ->
	let e1 = g' env e1 in
	let e2 = g (M.add x e1 env) e2 in
	concat e1 xts e2
     | _ -> assert false)
and g' env = function
  | If(c, x, y, e1, e2) ->
     let e1 = g env e1 in
     let e2 = g env e2 in
     h env (If(c, x, y, e1, e2))
  | FIf(c, x, y, e1, e2) ->
     let e1 = g env e1 in
     let e2 = g env e2 in
     h env (FIf(c, x, y, e1, e2))
  | IfThen(f, e, t) ->
     assert (List.length t = 0); 
     let e = g env e in
     h env (IfThen(f, e, t))
  | e -> h env e

let rec j e =
  let e' = g M.empty e in
  if e = e' then
    e'
  else
    j e'
     
let i { name = l; args = xs; body = e; ret = t } =
  { name = l; args = xs; body = j e; ret = t }
     
let f (Prog(data, vars, fundefs, e)) =
  Prog(data, vars, List.map i fundefs, j e)
