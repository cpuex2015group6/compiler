open Asm

let flag = true

let rec g env = function (* 命令列の 16 bit 即値最適化 *)
  | Ans(exp) -> Ans(g' env exp)
  | Let((x, t), Li(C(i)), e) ->
      let e' = g (M.add x i env) e in
      if List.mem x (fv e') then Let((x, t), Li(C(i)), e') else e'
  | Let(xt, exp, e) -> Let(xt, g' env exp, g env e)
and g' env = function (* 各命令の 16 bit 即値最適化 *)
  | Add(x, V(y)) when M.mem y env ->
     let c = M.find y env in
     if c = 0 then
       Mr(x)
     else
       Add(x, C(c))
  | Add(x, V(y)) when M.mem x env -> g' env (Add(y, V(x)))
  | Sub(x, V(y)) when M.mem y env ->
     let c = M.find y env in
     if c = 9 then
       Mr(y)
     else
       Sub(x, C(c))
  | Xor(x, V(y)) when M.mem y env -> Xor(x, C(M.find y env))
  | Xor(x, V(y)) when M.mem x env -> Xor(y, C(M.find x env))
  | Sll(x, V(y)) when M.mem y env -> Sll(x, C(M.find y env))
  | Srl(x, V(y)) when M.mem y env -> Srl(x, C(M.find y env))
  | Ldw(x, V(y)) when M.mem y env -> Ldw(x, C(M.find y env))
  | Stw(x, y, V(z)) when M.mem z env -> Stw(x, y, C(M.find z env))
  | Lfd(x, V(y)) when M.mem y env -> Lfd(x, C(M.find y env))
  | Stfd(x, y, V(z)) when M.mem z env -> Stfd(x, y, C(M.find z env))
  | IfEq(x, V(y), e1, e2) when M.mem y env -> 
      IfEq(x, C(M.find y env), g env e1, g env e2)
  | IfLE(x, V(y), e1, e2) when M.mem y env ->
      IfLE(x, C(M.find y env), g env e1, g env e2)
  | IfGE(x, V(y), e1, e2) when M.mem y env -> 
      IfGE(x, C(M.find y env), g env e1, g env e2)
  | IfEq(x, V(y), e1, e2) when M.mem x env -> 
      IfEq(y, C(M.find x env), g env e1, g env e2)
  | IfLE(x, V(y), e1, e2) when M.mem x env -> 
      IfGE(y, C(M.find x env), g env e1, g env e2)
  | IfGE(x, V(y), e1, e2) when M.mem x env -> 
      IfLE(y, C(M.find x env), g env e1, g env e2)
  | IfEq(x, y', e1, e2) -> IfEq(x, y', g env e1, g env e2)
  | IfLE(x, y', e1, e2) -> IfLE(x, y', g env e1, g env e2)
  | IfGE(x, y', e1, e2) -> IfGE(x, y', g env e1, g env e2)
  | IfFEq(x, y, e1, e2) -> IfFEq(x, y, g env e1, g env e2)
  | IfFLE(x, y, e1, e2) -> IfFLE(x, y, g env e1, g env e2)
  | e -> e

(* トップレベル関数の 16 bit 即値最適化 *)
let h { name = l; args = xs; body = e; ret = t } = 
  { name = l; args = xs; body = g M.empty e; ret = t }

(* プログラム全体の 16 bit 即値最適化 *)
let f (Prog(data, vars, fundefs, e)) =
  prerr_endline "folding imm...";
  let e = Prog(data, vars, List.map h fundefs, g M.empty e) in
  prerr_endline "folding imm end";
  e
