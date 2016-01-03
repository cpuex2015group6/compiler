(* レジスタ割り当て後の最適化パターンの登録と実行 *)

open Asm

exception Unmatched

let rec check_ans f  = function
  | Ans(exp) -> check_ans_exp f exp
  | Let(_, _, e) -> check_ans f e
and check_ans_exp f = function
  | If(_, _, _, e1, e2) | FIf(_, _, _, e1, e2) -> check_ans f e1 && check_ans f e2
  | IfThen(_, e, _) -> check_ans f e && check_ans_exp f (Li(C(0)))
  | exp -> f exp
    
let rec replace_ans exp = function
  | Ans(exp') -> Ans(replace_ans_exp exp exp')
  | Let(xts, exp', e) -> Let(xts, exp', replace_ans exp e)
and replace_ans_exp exp = function
  | If(c, x, y, e1, e2) -> If(c, x, y, replace_ans exp e1, replace_ans exp e2)
  | FIf(c, x, y, e1, e2) -> FIf(c, x, y, replace_ans exp e1, replace_ans exp e2)
  | IfThen(f, e, t) -> IfThen(f, replace_ans exp e, t)
  | _ -> exp

  
let pat = [
  (fun dest -> function
  | Mr(x)
      when (try List.fold_left2 (fun f d z -> f && (d = z)) true dest [x]
	with Invalid_argument _ -> false) ->
     Ans(Nop);
  | _ -> raise Unmatched);
  (fun dest -> function
  | Tuple(xs)
      when (try List.fold_left2 (fun f d z -> f && (d = z)) true dest xs
	with Invalid_argument _ -> false) ->
     Ans(Nop);
  | _ -> raise Unmatched);
  (fun dest -> function
  | If(c, x, y, Ans(Nop), Ans(Nop)) ->
     Ans(Nop);
  | _ -> raise Unmatched);
  (fun dest -> function
  | If(c, x, y, Ans(Nop), e) ->
     Ans(If(negcond c, x, y, e, Ans(Nop)));
  | _ -> raise Unmatched);
  (fun dest -> function
  | FIf(c, x, y, Ans(Nop), e) ->
     Ans(FIf(negcond c, x, y, e, Ans(Nop)));
  | _ -> raise Unmatched);
  (* どっちもMrなら事故る *)
  (fun dest -> function
  | If(c, x, y, (Ans(Mr(_)) as e1), e2) ->
     Ans(If(negcond c, x, y, e2, e1));
  | _ -> raise Unmatched);
  (fun dest -> function
  | FIf(c, x, y, (Ans(Mr(_)) as e1), e2) ->
     Ans(FIf(negcond c, x, y, e2, e1));
  | _ -> raise Unmatched);
  (fun dest -> function
  | If(c, x, y, (Ans(Tuple(_)) as e1), e2) ->
     Ans(If(negcond c, x, y, e2, e1));
  | _ -> raise Unmatched);
  (fun dest -> function
  | FIf(c, x, y, (Ans(Tuple(_)) as e1), e2) ->
     Ans(FIf(negcond c, x, y, e2, e1));
  | _ -> raise Unmatched);
  (fun dest -> function
  | If(c, x, y, e1, Ans(Mr(z)))
      when (try List.fold_left2 (fun f d z -> f && (d = z)) true dest [z]
	with Invalid_argument _ -> false) ->
     Ans(If(c, x, y, e1, Ans(Nop)));
  | _ -> raise Unmatched);
  (fun dest -> function
  | FIf(c, x, y, e1, Ans(Mr(z)))
      when (try List.fold_left2 (fun f d z -> f && (d = z)) true dest [z]
	with Invalid_argument _ -> false) ->
     Ans(FIf(c, x, y, e1, Ans(Nop)));
  | _ -> raise Unmatched);
  (fun dest -> function
  | If(c, x, y, e1, Ans(Tuple(z)))
      when (try List.fold_left2 (fun f d z -> f && (d = z)) true dest z
	with Invalid_argument _ -> false) ->
     Ans(If(c, x, y, e1, Ans(Nop)));
  | _ -> raise Unmatched);
  (fun dest -> function
  | FIf(c, x, y, e1, Ans(Tuple(z)))
      when (try List.fold_left2 (fun f d z -> f && (d = z)) true dest z
	with Invalid_argument _ -> false) ->
     Ans(FIf(c, x, y, e1, Ans(Nop)));
  | _ -> raise Unmatched);
]

let h dest e = 
  match List.fold_left (fun a p ->
    match a with
    | Some (Ans(e)) -> (try Some (p dest e) with Unmatched -> Some (Ans(e)))
    | Some _ -> a
    | None -> (try Some (p dest e) with Unmatched -> None)) None pat with
  | Some x -> x
  | None -> Ans(e)
  
let rec g dest = function
  | Ans(exp) -> g' dest exp
  | Let(dest', exp, Ans(Nop)) when (try List.fold_left2 (fun f dest dest' -> f && (dest = dest')) true dest (rm_t dest') with Invalid_argument _ -> false) -> g' dest exp
  | Let(xts, exp, e) ->
     let exp = g' (rm_t xts) exp in
     let e = g dest e in
     (match exp with
     | Ans(Nop) ->
	e
     | _ ->
	concat exp xts e)
and g' dest = function
  | If(c, x, y, e1, e2) ->
     let e1 = g dest e1 in
     let e2 = g dest e2 in
     h dest (If(c, x, y, e1, e2))
  | FIf(c, x, y, e1, e2) ->
     let e1 = g dest e1 in
     let e2 = g dest e2 in
     h dest (FIf(c, x, y, e1, e2))
  | IfThen(f, e, t) ->
     let e = g dest e in
     h dest (IfThen(f, e, t))
  | e -> h dest e

let rec j e =
  let e' = g [regs.(0)] e in
  if e = e' then
    e'
  else
    j e'
     
let i { name = l; args = xs; body = e; ret = t } =
  { name = l; args = xs; body = j e; ret = t }
     
let f (Prog(data, vars, fundefs, e)) =
  Prog(data, vars, List.map i fundefs, j e)
