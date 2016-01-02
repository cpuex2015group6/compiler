(* 無駄なレジスタムーブメント、letの除去 *)

open Asm

let genfv e = e, fv_exp e

let replace env x = try M.find x env with Not_found -> x
let replace' env x' =
  match x' with
  | V(x) -> V(replace env x)
  | c -> c
  
let rec g env = function
  | Ans(exp) ->
     let e', fvs = g' env exp in
     Ans(e'), fvs
  | Let(xts, (Li(C(i)) as exp), e) ->
     (match xts with
     | [(x, t)] ->
	let e, fvs_e = g env e in
	let exp, fvs_exp = g' env exp in
	if List.mem x fvs_e then
	  Let(xts, exp, e), fv_let (rm_t xts) fvs_exp fvs_e
	else
	  e, fvs_e
     | _ -> assert false)
  | Let(xts, exp, e) ->
     (match xts with
     | [(x, t)] ->
	let e, fvs_e = g env e in
	let exp, fvs_exp = g' env exp in
	if List.mem x fvs_e || effect exp || is_reg x then
	  match exp with
	  | Mr(x') when not (List.mem x' fvs_e)->
	     g (M.add x x' env) e
	  | _ ->
	     Let(xts, exp, e), fv_let (rm_t xts) fvs_exp fvs_e
	else
	  e, fvs_e
     | _ -> assert false)
and g' env = function
  | Nop | Li(_) | SetL(_) | Comment(_) | Save(_) | Restore(_) as e -> genfv e
  | Mr(x) -> genfv (Mr(replace env x))
  | Tuple _ -> assert false
  | Add(x, y') -> genfv (Add(replace env x, replace' env y'))
  | Sub(x, y') -> genfv (Sub(replace env x, replace' env y'))
  | Xor(x, y') -> genfv (Xor(replace env x, replace' env y'))
  | Or(x, y') -> genfv (Or(replace env x, replace' env y'))
  | And(x, y') -> genfv (And(replace env x, replace' env y'))
  | Sll(x, y') -> genfv (Sll(replace env x, replace' env y'))
  | Srl(x, y') -> genfv (Srl(replace env x, replace' env y'))
  | Ldw(x, y') -> genfv (Ldw(replace env x, replace' env y'))
  | Stw(x, y, z') -> genfv (Stw(replace env x, replace env y, replace' env z'))
  | FAdd(x, y) -> genfv (FAdd(replace env x, replace env y))
  | FSub(x, y) -> genfv (FSub(replace env x, replace env y))
  | FMul(x, y) -> genfv (FMul(replace env x, replace env y))
  | FDiv(x, y) -> genfv (FDiv(replace env x, replace env y))
  | FAbA(x, y) -> genfv (FAbA(replace env x, replace env y))
  | FAbs(x) -> genfv (FAbs(replace env x))
  | Sqrt(x) -> genfv (Sqrt(replace env x))
  | In -> genfv (In)
  | Out(x) -> genfv (Out(replace env x))
  | Count -> genfv (Count)
  | ShowExec -> genfv (ShowExec)
  | SetCurExec -> genfv (SetCurExec)
  | GetExecDiff -> genfv (GetExecDiff)
  | GetHp -> genfv (GetHp)
  | SetHp(x') -> genfv (SetHp(replace' env x'))
  | Cmp(c, x, y') -> genfv (Cmp(c, replace env x, replace' env y'))
  | FCmp(c, x, y) -> genfv (FCmp(c, replace env x, replace env y))
  | Cmpa(c, x, y', z) -> genfv (Cmpa(c, replace env x, replace' env y', replace env z))
  | FCmpa(c, x, y, z) -> genfv (FCmpa(c, replace env x, replace env y, replace env z))
  | If(c, x, y, e1, e2) ->
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let x = replace env x in
     let y = replace env y in
     If(c, x, y, e1, e2), fv_if x y fve1 fve2
  | FIf(c, x, y, e1, e2) ->
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let x = replace env x in
     let y = replace env y in
     FIf(c, x, y, e1, e2), fv_if x y fve1 fve2
  | IfThen(f, e, t) ->
     assert (List.length t = 0); 
     let e, fve = g env e in
     let f = replace env f in
     IfThen(f, e, t), fv_ifthen f fve t
  | CallCls(x, ys) -> genfv (CallCls(x, List.map (fun y -> replace env y) ys))
  | CallDir(x, ys) -> genfv (CallDir(x, List.map (fun y -> replace env y) ys))
  
let i { name = l; args = xs; body = e; ret = t } =
  { name = l; args = xs; body = fst (g M.empty e); ret = t }
  
let f (Prog(data, vars, fundefs, e)) =
  Prog(data, vars, List.map i fundefs, fst (g M.empty e))
