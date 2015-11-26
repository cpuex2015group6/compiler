open Asm

let flag = true

let rec g env = function (* 命令列の 16 bit 即値最適化 *)
  | Ans(exp) ->
     let e', fvs = g' env exp in
     Ans(e'), fvs
  | Let((x, t), Li(C(i)), e) ->
      let e', fvs = g (M.add x i env) e in
      if List.mem x fvs then Let((x, t), Li(C(i)), e'), fv_let x (fv_exp (Li(C(i)))) fvs else e', fvs
  | Let((x, t), exp, e) ->
     let exp', fvs_exp = g' env exp in
     let e', fvs_e = g env e in
     Let((x, t), exp', e'), fv_let x fvs_exp fvs_e
and g' env = function (* 各命令の 16 bit 即値最適化 *)
  | Add(x, V(y)) when M.mem y env ->
     let c = M.find y env in
     if c = 0 then
       let e = Mr(x) in
       e, fv_exp e
     else
       let e = Add(x, C(c)) in
       e, fv_exp e
  | Add(x, V(y)) when M.mem x env -> g' env (Add(y, V(x)))
  | Sub(x, V(y)) when M.mem y env ->
     let c = M.find y env in
     if c = 0 then
       let e = Mr(y) in
       e, fv_exp e
     else
       let e = Sub(x, C(c)) in
       e, fv_exp e
  | Xor(x, V(y)) when M.mem y env ->
     let e = Xor(x, C(M.find y env)) in
     e, fv_exp e
  | Xor(x, V(y)) when M.mem x env ->
     let e = Xor(y, C(M.find x env)) in
     e, fv_exp e
  | Sll(x, V(y)) when M.mem y env ->
     let e = Sll(x, C(M.find y env)) in
     e, fv_exp e
  | Srl(x, V(y)) when M.mem y env ->
     let e = Srl(x, C(M.find y env)) in
     e, fv_exp e
  | Ldw(x, V(y)) when M.mem x env &&  M.mem y env ->
     let e = Ldw(reg_zero, C((M.find x env) + (M.find y env))) in
     e, fv_exp e
  | Ldw(x, V(y)) when M.mem y env ->
     let e = Ldw(x, C(M.find y env)) in
     e, fv_exp e
  | Stw(x, y, V(z)) when M.mem y env && M.mem z env ->
     let e = Stw(x, reg_zero, C((M.find y env) + (M.find z env))) in
     e, fv_exp e
  | Stw(x, y, V(z)) when M.mem z env ->
     let e = Stw(x, y, C(M.find z env)) in
     e, fv_exp e
  | Lfd(x, V(y)) when M.mem y env ->
     let e = Lfd(x, C(M.find y env)) in
     e, fv_exp e
  | Stfd(x, y, V(z)) when M.mem z env ->
     let e = Stfd(x, y, C(M.find z env)) in
     e, fv_exp e
  | IfEq(x, V(y), e1, e2) when M.mem y env ->
     let c = M.find y env in
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_if x (V(y)) fve1 fve2 in
     if c = 0 then
       IfEq(x, V(reg_zero), e1, e2), fv
     else
       IfEq(x, C(c), e1, e2), fv
  | IfLE(x, V(y), e1, e2) when M.mem y env ->
     let c = M.find y env in
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_if x (V(y)) fve1 fve2 in
     if c = 0 then
       IfLE(x, V(reg_zero), e1, e2), fv
     else
       IfLE(x, C(c), e1, e2), fv
  | IfGE(x, V(y), e1, e2) when M.mem y env -> 
     let c = M.find y env in
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_if x (V(y)) fve1 fve2 in
     if c = 0 then
       IfGE(x, V(reg_zero), e1, e2), fv
     else
       IfGE(x, C(c), e1, e2), fv
  | IfEq(x, V(y), e1, e2) when M.mem x env -> 
     let c = M.find x env in
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_if x (V(y)) fve1 fve2 in
     if c = 0 then
       IfEq(y, V(reg_zero), e1, e2), fv
     else
       IfEq(y, C(c), e1, e2), fv
  | IfLE(x, V(y), e1, e2) when M.mem x env -> 
     let c = M.find x env in
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_if x (V(y)) fve1 fve2 in
     if c = 0 then
       IfGE(y, V(reg_zero), e1, e2), fv
     else
       IfGE(y, C(c), e1, e2), fv
  | IfGE(x, V(y), e1, e2) when M.mem x env -> 
     let c = M.find x env in
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_if x (V(y)) fve1 fve2 in
     if c = 0 then
       IfLE(y, V(reg_zero), e1, e2), fv
     else
       IfLE(y, C(c), e1, e2), fv
  | IfEq(x, y', e1, e2) ->
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_if x y' fve1 fve2 in
     IfEq(x, y', e1, e2), fv
  | IfLE(x, y', e1, e2) ->
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_if x y' fve1 fve2 in
     IfLE(x, y', e1, e2), fv
  | IfGE(x, y', e1, e2) ->
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_if x y' fve1 fve2 in
     IfGE(x, y', e1, e2), fv
  | IfFEq(x, y, e1, e2) when M.mem y env ->
     let c = M.find y env in
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_iff x y fve1 fve2 in
     if c = 0 then
       IfFEq(x, reg_zero, e1, e2), fv
     else
       IfFEq(x, y, e1, e2), fv
  | IfFLE(x, y, e1, e2) when M.mem y env ->
     let c = M.find y env in
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_iff x y fve1 fve2 in
     if c = 0 then
       IfFLE(x, reg_zero, e1, e2), fv
     else
       IfFLE(x, y, e1, e2), fv
  | IfFEq(x, y, e1, e2) when M.mem x env -> 
     let c = M.find x env in
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_iff x y fve1 fve2 in
     if c = 0 then
       IfFEq(y, reg_zero, e1, e2), fv
     else
       IfFEq(y, x, e1, e2), fv
  | IfFLE(x, y, e1, e2) when M.mem x env -> 
     let c = M.find x env in
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_iff x y fve1 fve2 in
     if c = 0 then
       IfFLE(reg_zero, y, e1, e2), fv
     else
       IfFLE(x, y, e1, e2), fv
  | IfFEq(x, y, e1, e2) ->
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_iff x y fve1 fve2 in
     IfFEq(x, y, e1, e2), fv
  | IfFLE(x, y, e1, e2) ->
     let e1, fve1 = g env e1 in
     let e2, fve2 = g env e2 in
     let fv = fv_iff x y fve1 fve2 in
     IfFLE(x, y, e1, e2), fv
  | e -> e, fv_exp e

(* トップレベル関数の 16 bit 即値最適化 *)
let h { name = l; args = xs; body = e; ret = t } =
  let e, _ = g M.empty e in
  { name = l; args = xs; body = e; ret = t }

(* プログラム全体の 16 bit 即値最適化 *)
let f (Prog(data, vars, fundefs, e)) =
  prerr_endline "folding imm...";
  let e, _ = g M.empty e in
  let e = Prog(data, vars, List.map h fundefs, e) in
  prerr_endline "folding imm end";
  e
