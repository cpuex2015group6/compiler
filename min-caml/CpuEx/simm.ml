open Asm

let rmzero env x =
  try (if M.find x env = 0 then reg_zero else (if M.find x env = -1 then reg_m1 else x)) with Not_found -> x
    
let rec g env = function (* 命令列の 16 bit 即値最適化 *)
  | Ans(exp) -> Ans(g' env exp)
  | Let((x, t), Li(C(i)), e) -> Let((x, t), Li(C(i)), g (M.add x i env) e)
  | Let((x, t), Mr(y), e) when M.mem y env ->
     let i = M.find y env in
     Let((x, t), Li(C(i)), g (M.add x i env) e)
  | Let((x, t), exp, e) -> Let((x, t), g' env exp, g env e)
and g' env e =
  let e = match e with
    | Mr(x) -> Mr(rmzero env x)
    | Union _ -> assert false
    | Add(x, V(y)) -> Add(rmzero env x, V(rmzero env y))
    | Add(x, C(c)) -> Add(rmzero env x, C(c))
    | Sub(x, V(y)) -> Sub(rmzero env x, V(rmzero env y))
    | Sub(x, C(c)) -> Sub(rmzero env x, C(c))
    | Xor(x, V(y)) -> Xor(rmzero env x, V(rmzero env y))
    | Xor(x, C(c)) -> Xor(rmzero env x, C(c))
    | Or(x, V(y)) -> Or(rmzero env x, V(rmzero env y))
    | Or(x, C(c)) -> Or(rmzero env x, C(c))
    | And(x, V(y)) -> And(rmzero env x, V(rmzero env y))
    | And(x, C(c)) -> And(rmzero env x, C(c))
    | Sll(x, V(y)) -> Sll(rmzero env x, V(rmzero env y))
    | Sll(x, C(c)) -> Sll(rmzero env x, C(c))
    | Srl(x, V(y)) -> Srl(rmzero env x, V(rmzero env y))
    | Srl(x, C(c)) -> Srl(rmzero env x, C(c))
    | Ldw(x, V(y)) -> Ldw(rmzero env x, V(rmzero env y))
    | Ldw(x, C(c)) -> Ldw(rmzero env x, C(c))
    | Stw(x, y, V(z)) -> Stw(rmzero env x, rmzero env y, V(rmzero env z))
    | Stw(x, y, C(c)) -> Stw(rmzero env x, y, C(c))
    | FAdd(x, y) -> FAdd(rmzero env x, rmzero env y)
    | FSub(x, y) -> FSub(rmzero env x, rmzero env y)
    | FMul(x, y) -> FMul(rmzero env x, rmzero env y)
    | FDiv(x, y) -> FDiv(rmzero env x, rmzero env y)
    | FAbA(x, y) -> FAbA(rmzero env x, rmzero env y)
    | FAbs(x) -> FAbs(rmzero env x)
    | Sqrt(x) -> Sqrt(rmzero env x)
    | Out(x) -> Out(rmzero env x)
    | SetHp(V(x)) -> SetHp(V(rmzero env x))
    | Cmp(cond, x, V(y)) -> Cmp(cond, rmzero env x, V(rmzero env y))
    | Cmp(cond, x, C(c)) -> Cmp(cond, rmzero env x, C(c))
    | FCmp(cond, x, y) -> FCmp(cond, rmzero env x, rmzero env y)
    | Cmpa(cond, x, V(y), z) -> Cmpa(cond, rmzero env x, V(rmzero env y), rmzero env z)
    | Cmpa(cond, x, C(c), z) -> Cmpa(cond, rmzero env x, C(c), rmzero env z)
    | FCmpa(cond, x, y, z) -> FCmpa(cond, rmzero env x, rmzero env y, rmzero env z)
    | If(c, x, y, e1, e2) -> If(c, rmzero env x, rmzero env y, e1, e2)
    | FIf(c, x, y, e1, e2) -> FIf(c, rmzero env x, rmzero env y, e1, e2)
    | IfThen(f, e) -> IfThen(rmzero env f, e)
    | Save(x, y) -> Save(rmzero env x, rmzero env y)
    | Restore(x) -> Restore(rmzero env x)
    | e -> e
  in
  g'' env e
and g'' env = function (* 各命令の 16 bit 即値最適化 *)
  | Add(x, V(y)) when M.mem y env -> Add(x, C(M.find y env))
  | Add(x, V(y)) when M.mem x env -> g'' env (Add(y, V(x)))
  | Sub(x, V(y)) when M.mem y env -> Sub(x, C(M.find y env))
(*  | Xor(x, V(y)) when M.mem y env -> Xor(x, C(M.find y env))
  | Xor(x, V(y)) when M.mem x env -> Xor(y, C(M.find x env))
  | Sll(x, V(y)) when M.mem y env -> Sll(x, C(M.find y env))
  | Srl(x, V(y)) when M.mem y env -> Srl(x, C(M.find y env))*)
  | Ldw(x, V(y)) when M.mem x env &&  M.mem y env -> Ldw(reg_zero, C((M.find x env) + (M.find y env)))
  | Ldw(x, V(y)) when M.mem y env -> Ldw(x, C(M.find y env))
  | Ldw(x, V(y)) when M.mem x env -> Ldw(y, C(M.find x env))
  | Stw(x, y, V(z)) when M.mem y env && M.mem z env -> Stw(x, reg_zero, C((M.find y env) + (M.find z env)))
  | Stw(x, y, V(z)) when M.mem y env -> Stw(x, z, C(M.find y env))
  | SetHp(V(x)) when M.mem x env -> SetHp(C(M.find x env))
  | Cmp(cond, x, V(y)) when M.mem y env ->
     let c : id_or_imm = C(M.find y env) in
     Cmp(cond, x, c)
  | Cmp(cond, x, V(y)) when M.mem x env ->
     let c : id_or_imm = C(M.find x env) in
     Cmp(Asm.swapcond cond, y, c)
  | Cmpa(cond, x, V(y), z) when M.mem y env ->
     let c : id_or_imm = C(M.find y env) in
     Cmpa(cond, x, c, z)
  | Cmpa(cond, x, V(y), z) when M.mem x env ->
     let c : id_or_imm = C(M.find x env) in
     Cmpa(Asm.swapcond cond, y, c, z)
  | If(c, x, y, e1, e2) ->
     let e1 = g env e1 in
     let e2 = g env e2 in
     If(c, x, y, e1, e2)
  | FIf(c, x, y, e1, e2) ->
     let e1 = g env e1 in
     let e2 = g env e2 in
     FIf(c, x, y, e1, e2)
  | IfThen(f, e) ->
     let e = g env e in
     IfThen(f, e)
  | e -> e

let rec i e =
  let e' = g M.empty e in
  if e = e' then
    e'
  else
    i e'

(* トップレベル関数の 16 bit 即値最適化 *)
let h { name = l; args = xs; body = e; ret = t } =
  { name = l; args = xs; body = i e; ret = t }

(* プログラム全体の 16 bit 即値最適化 *)
let f (Prog(data, vars, fundefs, e)) =
  Prog(data, vars, List.map h fundefs, i e)
