open Asm

let rmzero env x =
  try (if M.find x env = 0 then reg_zero else (if M.find x env = -1 then reg_m1 else x)) with Not_found -> x
  
let rec g env = function (* 命令列の 16 bit 即値最適化 *)
  | Ans(exp) ->
     let e', fvs = g' env exp in
     Ans(e'), fvs
  | Let((x, t), Li(C(i)), e) ->
      let e', fvs = g (M.add x i env) e in
      if List.mem x fvs then Let((x, t), Li(C(i)), e'), fv_let x (fv_exp (Li(C(i)))) fvs else e', fvs
  | Let((x, t), Mr(y), e) when M.mem y env ->
     let i = M.find y env in
     let e', fvs = g (M.add x i env) e in
     if List.mem x fvs then Let((x, t), Li(C(i)), e'), fv_let x (fv_exp (Li(C(i)))) fvs else e', fvs
  | Let((x, t), exp, e) ->
     let exp', fvs_exp = g' env exp in
     let e', fvs_e = g env e in
     Let((x, t), exp', e'), fv_let x fvs_exp fvs_e
and g' env e =
  let e = match e with
    | Mr(x) -> Mr(rmzero env x)
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
    | FMr(x) -> FMr(rmzero env x)
    | FAdd(x, y) -> FAdd(rmzero env x, rmzero env y)
    | FSub(x, y) -> FSub(rmzero env x, rmzero env y)
    | FMul(x, y) -> FMul(rmzero env x, rmzero env y)
    | FDiv(x, y) -> FDiv(rmzero env x, rmzero env y)
    | FAbA(x, y) -> FAbA(rmzero env x, rmzero env y)
    | FAM(x, y, z) -> FAM(rmzero env x, rmzero env y, rmzero env z)
    | FAbs(x) -> FAbs(rmzero env x)
    | Sqrt(x) -> Sqrt(rmzero env x)
    | Lfd(x, V(y)) -> Lfd(rmzero env x, V(rmzero env y))
    | Lfd(x, C(c)) -> Lfd(rmzero env x, C(c))
    | Stfd(x, y, V(z)) -> Stfd(rmzero env x, rmzero env y, V(rmzero env z))
    | Stfd(x, y, C(c)) -> Stfd(rmzero env x, y, C(c))
    | Out(x) -> Out(rmzero env x)
    | SetHp(V(x)) -> SetHp(V(rmzero env x))
    | Cmp(cond, x, V(y)) -> Cmp(cond, rmzero env x, V(rmzero env y))
    | Cmp(cond, x, C(c)) -> Cmp(cond, rmzero env x, C(c))
    | FCmp(cond, x, y) -> FCmp(cond, rmzero env x, rmzero env y)
    | If(c, x, y, e1, e2) -> If(c, rmzero env x, rmzero env y, e1, e2)
    | FIf(c, x, y, e1, e2) -> FIf(c, rmzero env x, rmzero env y, e1, e2)
    | Save(x, y) -> Save(rmzero env x, rmzero env y)
    | Restore(x) -> Restore(rmzero env x)
    | e -> e
  in
  g'' env e
and g'' env = function (* 各命令の 16 bit 即値最適化 *)
  | Add(x, V(y)) when M.mem y env ->
     let e = Add(x, C(M.find y env)) in
     e, fv_exp e
  | Add(x, V(y)) when M.mem x env -> g'' env (Add(y, V(x)))
  | Sub(x, V(y)) when M.mem y env ->
     let e = Sub(x, C(M.find y env)) in
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
  | Ldw(x, V(y)) when M.mem x env ->
     let e = Ldw(y, C(M.find x env)) in
     e, fv_exp e
  | Stw(x, y, V(z)) when M.mem y env && M.mem z env ->
     let e = Stw(x, reg_zero, C((M.find y env) + (M.find z env))) in
     e, fv_exp e
  | Stw(x, y, V(z)) when M.mem y env ->
     let e = Stw(x, z, C(M.find y env)) in
     e, fv_exp e
  | Lfd(x, V(y)) when M.mem y env ->
     let e = Lfd(x, C(M.find y env)) in
     e, fv_exp e
  | Stfd(x, y, V(z)) when M.mem z env ->
     let e = Stfd(x, y, C(M.find z env)) in
     e, fv_exp e
  | SetHp(V(x)) when M.mem x env ->
     let e = SetHp(C(M.find x env)) in
     e, fv_exp e
  | Cmp(cond, x, V(y)) when M.mem y env ->
     let c : id_or_imm = C(M.find y env) in
     let e = Cmp(cond, x, c) in
     e, fv_exp e
  | Cmp(cond, x, V(y)) when M.mem x env ->
     let c : id_or_imm = C(M.find x env) in
     let e = Cmp(Asm.swapcond cond, y, c) in
     e, fv_exp e
  | If(c, x, y, e1, e2) ->
     (
       match e1, e2 with
       | Ans(Li (C(1))), Ans(Li (C(0))) ->
	  g'' env (Cmp(c, x, V(y)))
       | Ans(Li (C(0))), Ans(Li (C(1))) ->
	  g'' env (Cmp(Asm.negcond c, x, V(y)))
       | _ ->
	  let e1, fve1 = g env e1 in
	  let e2, fve2 = g env e2 in
	  let fv = fv_if x y fve1 fve2 in
	  If(c, x, y, e1, e2), fv
     )
  | FIf(c, x, y, e1, e2) ->
     (
       match e1, e2 with
       | Ans(Li (C(1))), Ans(Li (C(0))) ->
	  g'' env (FCmp(c, x, y))
       | Ans(Li (C(0))), Ans(Li (C(1))) ->
	  g'' env (FCmp(Asm.negcond c, x, y))
       | _ ->
	  let e1, fve1 = g env e1 in
	  let e2, fve2 = g env e2 in
	  let fv = fv_if x y fve1 fve2 in
	  FIf(c, x, y, e1, e2), fv
     )
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
