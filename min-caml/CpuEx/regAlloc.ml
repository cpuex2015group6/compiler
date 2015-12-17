open Asm

exception DepReg

(* for register coalescing *)
(* [XXX] Callがあったら、そこから先は無意味というか逆効果なので追わない。
         そのために「Callがあったかどうか」を返り値の第1要素に含める。 *)
let rec target' src (dest, t) = function
  | Mr(x) when x = src && is_reg dest ->
      assert (t <> Type.Unit);
      false, [], [dest]
  | If(_, _, _, e1, e2)| FIf(_, _, _, e1, e2) ->
      let c1, rsf1, rs1 = target src (dest, t) e1 in
      let c2, rsf2, rs2 = target src (dest, t) e2 in
      c1 && c2, rsf1 @ rsf2, rs1 @ rs2
  | IfThen(_, e) -> target src (dest, t) e
  | CallCls(x, ys) ->
     true, [], (target_args src regs 0 ys @
              if x = src then [reg_cl] else [])
  | CallDir(_, ys) ->
     true, [], (target_args src regs 0 ys)
  | Cmpa(_, _, _, c) | FCmpa(_, _, _, c) when c = src ->
     if is_reg dest then
       false, [dest], []
     else
       raise DepReg
  | _ -> false, [], []
and target src dest = function (* register targeting (caml2html: regalloc_target) *)
  | Ans(exp) -> target' src dest exp
  | Let(xt, exp, e) ->
      let c1, rsf1, rs1 = target' src xt exp in
      if c1 then true, rsf1, rs1 else
      let c2, rsf2, rs2 = target src dest e in
      c2, rsf1 @ rsf2, rs1 @ rs2
and target_args src all n = function (* auxiliary function for Call *)
  | [] -> []
  | y :: ys when src = y -> all.(n) :: target_args src all (n + 1) ys
  | _ :: ys -> target_args src all (n + 1) ys

type alloc_result = (* allocにおいてspillingがあったかどうかを表すデータ型 *)
  | Alloc of Id.t (* allocated register *)
  | Spill of Id.t (* spilled variable *)
let alloc dest cont contfv regenv x t =
  (* allocate a register or spill a variable *)
  assert (not (M.mem x regenv));
  let all =
    match t with
    | Type.Unit -> ["%r00"] (* dummy *)
    | _ -> allregs in
  if all = ["%r00"] then Alloc("%r00") else (* [XX] ad hoc optimization *)
    if is_reg x then Alloc(x) else
      let free = contfv in
      try
	let (_, forth, prefer) = target x dest cont in
	let r = try List.hd forth with Failure "hd" ->
	  let live = (* 生きているレジスタ *)
	    List.fold_left
              (fun live y ->
		if is_reg y then S.add y live else
		  try let y' = M.find y regenv in if is_reg y' then S.add y' live else live
		  with Not_found -> live)
              (S.singleton reg_cl)
              free in
	  (* そうでないレジスタを探す *)
	  List.find
            (fun r -> not (S.mem r live))
            (prefer @ all)
	in
	(* Format.eprintf "allocated %s to %s@." x r; *)
	Alloc(r)
      with Not_found ->
	Format.eprintf "register allocation failed for %s@." x;
	let rec remove x = function
	  | [] -> []
	  | y::ys when x = y -> remove x ys
	  | y::ys -> y::(remove x ys)
	in
	let checkif_spillable y =
	  not (is_reg y) &&
	    try List.mem (M.find y regenv) (remove reg_cl all)
	    with Not_found -> false
	in
	let y = List.find checkif_spillable (List.rev free)
	in
	Format.eprintf "spilling %s from %s@." y (M.find y regenv);
	Spill(y)

(* auxiliary function for g and g'_and_restore *)
let add x r regenv =
  if is_reg x then (assert (x = r); regenv) else
  M.add x r regenv

(* auxiliary functions for g' *)
exception NoReg of Id.t * Type.t
let find x t regenv =
  if is_reg x then x else
  try M.find x regenv
  with Not_found -> raise (NoReg(x, t))
let find' x' regenv =
  match x' with
  | V(x) -> V(find x Type.Int regenv)
  | c -> c

let rec g dest cont contfv regenv = function (* 命令列のレジスタ割り当て (caml2html: regalloc_g) *)
  | Ans(exp) -> g'_and_restore dest cont contfv regenv exp
  | Let((x, t) as xt, exp, e) ->
     assert (not (M.mem x regenv));
     let cont' = concat e dest cont in
     let contfv' = concatfv e dest contfv in
     let (e1', regenv1) = g'_and_restore xt cont' contfv' regenv exp in
     let reg = try alloc dest cont' contfv' regenv1 x t with DepReg -> Alloc(x) in
     (match reg with
      | Spill(y) ->
	 let r = M.find y regenv1 in
	 let (e2', regenv2) = g dest cont contfv (add x r (M.remove y regenv1)) e in
	 let save =
	   try Save(M.find y regenv, y)
	   with Not_found -> Nop in	    
	 (seq(save, concat e1' (r, t) e2'), regenv2)
      | Alloc(r) ->
	 let (e2', regenv2) = g dest cont contfv (add x r regenv1) e in
	 (concat e1' (r, t) e2', regenv2))
and g'_and_restore dest cont contfv regenv exp = (* 使用される変数をスタックからレジスタへRestore (caml2html: regalloc_unspill) *)
  try g' dest cont contfv regenv exp
  with NoReg(x, t) ->
    ((* Format.eprintf "restoring %s@." x;*)
     g dest cont contfv regenv (Let((x, t), Restore(x), Ans(exp))))
and g' dest cont contfv regenv = function (* 各命令のレジスタ割り当て (caml2html: regalloc_gprime) *)
  | Nop | Li _ | SetL _ | Comment _ | Save _ | Restore _ as exp -> (Ans(exp), regenv)
  | Mr(x) -> (Ans(Mr(find x Type.Int regenv)), regenv)
  | Add(x, y') -> (Ans(Add(find x Type.Int regenv, find' y' regenv)), regenv)
  | Sub(x, y') -> (Ans(Sub(find x Type.Int regenv, find' y' regenv)), regenv)
  | Xor(x, y') -> (Ans(Xor(find x Type.Int regenv, find' y' regenv)), regenv)
  | Or(x, y') -> (Ans(Or(find x Type.Int regenv, find' y' regenv)), regenv)
  | And(x, y') -> (Ans(And(find x Type.Int regenv, find' y' regenv)), regenv)
  | Sll(x, y') -> (Ans(Sll(find x Type.Int regenv, find' y' regenv)), regenv)
  | Srl(x, y') -> (Ans(Srl(find x Type.Int regenv, find' y' regenv)), regenv)
  | Ldw(x, y') -> (Ans(Ldw(find x Type.Int regenv, find' y' regenv)), regenv)
  | Stw(x, y, z') -> (Ans(Stw(find x Type.Int regenv, find y Type.Int regenv, find' z' regenv)), regenv)
  | FAdd(x, y) -> (Ans(FAdd(find x Type.Float regenv, find y Type.Float regenv)), regenv)
  | FSub(x, y) -> (Ans(FSub(find x Type.Float regenv, find y Type.Float regenv)), regenv)
  | FMul(x, y) -> (Ans(FMul(find x Type.Float regenv, find y Type.Float regenv)), regenv)
  | FDiv(x, y) -> (Ans(FDiv(find x Type.Float regenv, find y Type.Float regenv)), regenv)
  | FAbA(x, y) -> (Ans(FAbA(find x Type.Float regenv, find y Type.Float regenv)), regenv)
  | FAbs(x) -> (Ans(FAbs(find x Type.Float regenv)), regenv)
  | Sqrt(x) -> (Ans(Sqrt(find x Type.Float regenv)), regenv)
  | In -> (Ans(In), regenv)
  | Out(x) -> (Ans(Out(find x Type.Int regenv)), regenv)
  | Count -> (Ans(Count), regenv)
  | ShowExec -> (Ans(ShowExec), regenv)
  | SetCurExec -> (Ans(SetCurExec), regenv)
  | GetExecDiff -> (Ans(GetExecDiff), regenv)
  | GetHp -> (Ans(GetHp), regenv)
  | SetHp(x') -> (Ans(SetHp(find' x' regenv)), regenv)
  | Cmp(c, x, y') -> (Ans(Cmp(c, find x Type.Int regenv, find' y' regenv)), regenv)
  | FCmp(c, x, y) -> (Ans(FCmp(c, find x Type.Float regenv, find y Type.Float regenv)), regenv)
  | Cmpa(c, x, y', z) -> (Ans(Cmpa(c, find x Type.Int regenv, find' y' regenv, find z Type.Int regenv)), regenv)
  | FCmpa(c, x, y, z) -> (Ans(FCmpa(c, find x Type.Float regenv, find y Type.Float regenv, find z Type.Int regenv)), regenv)
  | If(c, x, y, e1, e2) as exp -> g'_if dest cont contfv regenv exp (fun e1' e2' -> If(c, find x Type.Int regenv, find y Type.Int regenv, e1', e2')) e1 e2
  | FIf(c, x, y, e1, e2) as exp -> g'_if dest cont contfv regenv exp (fun e1' e2' -> FIf(c, find x Type.Float regenv, find y Type.Float regenv, e1', e2')) e1 e2
  | IfThen(f, e) as exp -> g'_ifthen dest cont contfv regenv exp (fun e' -> IfThen(find f Type.Int regenv, e')) e
  | CallCls(x, ys) as exp -> g'_call dest cont contfv regenv exp (fun ys -> CallCls(find x Type.Int regenv, ys)) ys
  | CallDir(l, ys) as exp -> g'_call dest cont contfv regenv exp (fun ys -> CallDir(l, ys)) ys
and g'_if dest cont contfv regenv exp constr e1 e2 = (* ifのレジスタ割り当て (caml2html: regalloc_if) *)
  let (e1', regenv1) = g dest cont contfv regenv e1 in
  let (e2', regenv2) = g dest cont contfv regenv e2 in
  let regenv' = (* 両方に共通のレジスタ変数だけ利用 *)
    List.fold_left
      (fun regenv' x ->
        try
	  if is_reg x then regenv' else
          let r1 = M.find x regenv1 in
          let r2 = M.find x regenv2 in
          if r1 <> r2 then regenv' else
	  M.add x r1 regenv'
        with Not_found -> regenv')
      M.empty
      contfv in
  (List.fold_left
     (fun e x ->
       if x = fst dest || not (M.mem x regenv) || M.mem x regenv' then e else
       seq(Save(M.find x regenv, x), e)) (* そうでない変数は分岐直前にセーブ *)
     (Ans(constr e1' e2'))
     contfv,
   regenv')
and g'_ifthen dest cont contfv regenv exp constr e = (* ifthenのレジスタ割り当て (caml2html: regalloc_if) *)
  let (e', regenv1) = g dest cont contfv regenv e in
  let regenv' = (* 両方に共通のレジスタ変数だけ利用 *)
    List.fold_left
      (fun regenv' x ->
        try
	  if is_reg x then regenv' else
            let r1 = M.find x regenv1 in
	    M.add x r1 regenv'
        with Not_found -> regenv')
      M.empty
      contfv in
  (List.fold_left
     (fun e x ->
       if x = fst dest || not (M.mem x regenv) || M.mem x regenv' then e else
       seq(Save(M.find x regenv, x), e)) (* そうでない変数は分岐直前にセーブ *)
     (Ans(constr e'))
     contfv,
   regenv')
and g'_call dest cont contfv regenv exp constr ys = (* 関数呼び出しのレジスタ割り当て (caml2html: regalloc_call) *)
  (List.fold_left
     (fun e x ->
       if x = fst dest || not (M.mem x regenv) then e else
       seq(Save(M.find x regenv, x), e))
     (Ans(constr
	    (List.map (fun y -> find y Type.Int regenv) ys)))
     contfv,
   M.empty)
    
let h { name = Id.L(x); args = ys; body = e; ret = t } = (* 関数のレジスタ割り当て (caml2html: regalloc_h) *)
  let regenv = M.add x reg_cl M.empty in
  let (i, arg_regs, regenv) =
    List.fold_left
      (fun (i, arg_regs, regenv) y ->
       let r = regs.(i) in
       (i + 1,
	      arg_regs @ [r],
	      (assert (not (is_reg y));
	       M.add y r regenv)))
      (0, [], regenv)
      ys in
  let a =
    match t with
    | Type.Unit -> Id.gentmp Type.Unit
    | _ -> regs.(0) in
  let (e', regenv') = g (a, t) (Ans(Mr(a))) (fv (Ans(Mr(a)))) regenv e in
  let (e', regenv') = g (a, t) (Ans(Mr(a))) (fv (Ans(Mr(a)))) regenv e' in
  { name = Id.L(x); args = arg_regs; body = e'; ret = t }

let f (Prog(data, vars, fundefs, e)) = (* プログラム全体のレジスタ割り当て (caml2html: regalloc_f) *)
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)@.";
  let fundefs' = List.map h fundefs in
  let e', regenv' = g (Id.gentmp Type.Unit, Type.Unit) (Ans(Nop)) (fv (Ans(Nop))) M.empty e in
  let e', regenv' = g (Id.gentmp Type.Unit, Type.Unit) (Ans(Nop)) (fv (Ans(Nop))) M.empty e' in
  let p = Prog(data, vars, fundefs', e') in
  p
