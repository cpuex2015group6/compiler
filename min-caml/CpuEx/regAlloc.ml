open Asm

let showmap f (regmap, pregmap, graph) vrmap =
  Printf.fprintf stdout ">>>> regmap of %s >>>>\n" f;
  Printf.fprintf stdout "regmap:\n";
  List.iter (fun (x, y) -> Printf.fprintf stdout "%s %s\n" x y) regmap;
  Printf.fprintf stdout "pregmap:\n";
  List.iter (fun (x, y) -> Printf.fprintf stdout "%s %s\n" x y) pregmap;
  Printf.fprintf stdout "graph:\n";
  List.iter (fun (x, y) -> Printf.fprintf stdout "%s %s\n" x y) graph;
  Printf.fprintf stdout "vrmap:\n";
  M.iter (fun v r -> Printf.fprintf stdout "%s -> %s\n" v r) vrmap
  
  
let rec specify_ret at = function
  | Ans (exp) -> Let(at, exp, Ans(Nop))
  | Let(xt, exp, e) -> Let(xt, exp, specify_ret at e)

let rm_regfvs fv = S.fold (fun v s -> if is_reg v then s else S.add v s) fv S.empty
     
let rec g dest live contfv = function
  | Ans exp ->
     let map, fv = g' dest live S.empty exp in
     map, rm_regfvs fv
  | Let((x, t) as xt, exp, e) ->
     let (regmap', pregmap', graph') as map, contfv = g dest (if is_reg x then live else S.add x live) contfv e in
     let (regmap, pregmap, graph), fv = (g' xt live contfv exp) in
     let regmap, pregmap, graph = regmap @ regmap', pregmap @ pregmap', graph @ graph' in
     let graph = S.fold (fun v graph -> if S.mem v contfv && not (is_reg x) then (x, v)::graph else graph) live graph in
     (regmap, pregmap, graph), fvs_let x (rm_regfvs fv) contfv
and g' (dv, _ as dest) live contfv exp =
  match exp with
  | Nop | Li _ | SetL _ | Add _ | Sub _ | Xor _ | Or _ | And _ | Sll _ | Srl _ | Ldw _ | Stw _ | FAdd _ | FSub _ | FMul _ | FDiv _ | FAbA _ | FAbs _ | Sqrt _ | In | Out _ | Count | ShowExec | SetCurExec | GetExecDiff | GetHp | SetHp _ | Comment _ | Cmp _ | FCmp _ | CallCls _ | CallDir _ | Save _ | Restore _ ->
     ([], [], []), fvs_exp exp
  | Mr(x) -> ([], [(dv, x)], []), fvs_exp exp
  | Union(x, y) -> ([(x, y)], [(dv, x)], []), fvs_exp exp
  | Cmpa(_, _, _, w) | FCmpa(_, _, _, w)-> ([(dv, w)], [], []), fvs_exp exp
  | If(_, x, y, e1, e2) | FIf(_, x, y, e1, e2) ->
     let (regmap1, pregmap1, graph1), contfv1 = g dest live contfv e1 in
     let (regmap2, pregmap2, graph2), contfv2 = g dest live contfv e2 in
     (regmap1@regmap2, pregmap1@pregmap2, graph1@graph2), fvs_if x y contfv1 contfv2
  | IfThen(f, e) ->
     let (regmap, pregmap, graph), contfv' = g dest (if is_reg dv then live else S.add dv live) contfv e in
     ((dv, f)::regmap, pregmap, graph), fvs_ifthen f contfv'
       
exception RegNot_found of Id.t
    
let replace regenv r = try if is_reg r then r else M.find r regenv with Not_found -> raise (RegNot_found r)
let replace' regenv = function
  | V(x) -> V(replace regenv x)
  | c -> c
let mem r regenv = if is_reg r then true else M.mem r regenv


let rec replace_e regenv = function
  | Ans (exp) -> Ans(replace_exp regenv exp)
  | Let((x, t), exp, e) -> Let((replace regenv x, t), replace_exp regenv exp, replace_e regenv e)
and replace_exp regenv = function
  | Nop | Li _ | SetL _ | In | Count | ShowExec | SetCurExec | GetExecDiff | GetHp | Comment _ | Restore _ as exp -> exp
  | Mr(x) -> Mr(replace regenv x)
  | Union(x, y) -> Union(replace regenv x, replace regenv y)
  | Add(x, y') -> Add(replace regenv x, replace' regenv y')
  | Sub(x, y') -> Sub(replace regenv x, replace' regenv y')
  | Xor(x, y') -> Xor(replace regenv x, replace' regenv y')
  | Or(x, y') -> Or(replace regenv x, replace' regenv y')
  | And(x, y') -> And(replace regenv x, replace' regenv y')
  | Sll(x, y') -> Sll(replace regenv x, replace' regenv y')
  | Srl(x, y') -> Srl(replace regenv x, replace' regenv y')
  | Ldw(x, y') -> Ldw(replace regenv x, replace' regenv y')
  | Stw(x, y, z') -> Stw(replace regenv x, replace regenv y, replace' regenv z')
  | FAdd(x, y) -> FAdd(replace regenv x, replace regenv y)
  | FSub(x, y) -> FSub(replace regenv x, replace regenv y)
  | FMul(x, y) -> FMul(replace regenv x, replace regenv y)
  | FDiv(x, y) -> FDiv(replace regenv x, replace regenv y)
  | FAbA(x, y) -> FAbA(replace regenv x, replace regenv y)
  | FAbs(x) -> FAbs(replace regenv x)
  | Sqrt(x) -> Sqrt(replace regenv x)
  | Out(x) -> Out(replace regenv x)
  | SetHp(x') -> SetHp(replace' regenv x')
  | Cmp(c, x, y') -> Cmp(c, replace regenv x, replace' regenv y')
  | FCmp(c, x, y) -> FCmp(c, replace regenv x, replace regenv y)
  | Cmpa(c, x, y', z) -> Cmpa(c, replace regenv x, replace' regenv y', replace regenv z)
  | FCmpa(c, x, y, z) -> FCmpa(c, replace regenv x, replace regenv y, replace regenv z)
  | CallCls(l, ys) -> CallCls(l, List.fold_left (fun l y -> l@[replace regenv y]) [] ys)
  | CallDir(f, ys) -> CallDir(f, List.fold_left (fun l y -> l@[replace regenv y]) [] ys)
  | If(c, x, y, e1, e2) -> If(c, replace regenv x, replace regenv y, replace_e regenv e1, replace_e regenv e2)
  | FIf(c, x, y, e1, e2) -> FIf(c, replace regenv x, replace regenv y, replace_e regenv e1, replace_e regenv e2)
  | IfThen(f, e1) -> IfThen(replace regenv f, replace_e regenv e1)
  | Save(x, y) -> Save(replace regenv x, y)


let rec insert t (xt, exp) = function
  | Ans(exp') -> let tv = Id.gentmp t in Let((tv, t), exp', Let(xt, exp, Ans(Mr(tv))))
  | Let(yt, exp', e) -> Let(yt, exp', insert t (xt, exp) e)

let cl_vars contfv lcontfv regenv exp =
  M.fold (fun r r' (exp, regenv) ->
    if not (S.mem r contfv) then
      (* 使用しない変数はregenvから削除 *)
      exp, regenv
    else if not (S.mem r lcontfv) then
      (* Callまでに使用しない変数は退避 *)
      seq(Save(r', r), exp), regenv
    else
      exp, (M.add r r' regenv)
  ) regenv (exp, M.empty)
     
(* Callによるレジスタ再割当てコードの生成 *)
let rec i dest contfv lcontfv regenv = function
  | Ans exp ->
     (* Mrでtmp varを入れた方が良いかもしれない *)
     let exp, regenv = i' dest regenv contfv lcontfv exp in
     cl_vars contfv lcontfv regenv exp
  | Let((x, t) as xt, exp, e) ->
     let contfv' = concatfvs e dest contfv in
     let lcontfv' = lconcatfvs e dest lcontfv in
     let exp, regenv = i' xt regenv contfv' lcontfv' exp in
     let exp, regenv = cl_vars contfv' lcontfv' regenv exp in
     let e, regenv = i dest contfv lcontfv (M.add x x regenv) e in
     (concat exp xt e), regenv
and i' dest regenv contfv lcontfv exp =
  try i'' dest regenv contfv lcontfv exp with RegNot_found r ->
    let id = Id.genid r in
    let exp, regenv = i' dest (M.add r id regenv) contfv lcontfv exp in
    Let((id, Type.Int), Restore(r), exp), regenv
and i'' dest regenv contfv lcontfv exp =
  match exp with
  | If(c, x, y, e1, e2) ->
     let _, dt = dest in
     let tv = Id.gentmp dt in 
     let e1, regenv1 = i dest contfv lcontfv regenv e1 in
     let e2, regenv2 = i dest contfv lcontfv regenv e2 in
     let keys = M.fold (fun k _ s -> S.add k s) regenv2 (M.fold (fun k _ s -> S.add k s) regenv1 S.empty) in
     let e1, e2, e, regenv' = S.fold (fun k (e1, e2, e, regenv) ->
       let t1 = Id.genid k in
       let t2 = Id.genid k in
       match mem k regenv1, mem k regenv2 with
       | true, true ->
	  if replace regenv1 k = replace regenv2 k then
	    e1, e2, e, M.add k (replace regenv1 k) regenv
	  else
	    e1,
	    e2,
	    Let((t2, Type.Int), Union(replace regenv1 k, replace regenv2 k), e),
	    M.add k t2 regenv
       | false, false -> assert false
       | true, false ->
	  e1,
	 (insert dt ((t1, Type.Int), Restore(k)) e2),
	 Let((t2, Type.Int), Union(replace regenv1 k, t1), e),
	 M.add k t2 regenv
       | false, true ->
     	  (insert dt ((t1, Type.Int), Restore(k)) e1),
	 e2,
	 Let((t2, Type.Int), Union(t1, replace regenv2 k), e),
	 M.add k t2 regenv
     ) keys (e1, e2, Ans(Mr(tv)), M.empty) in
     Let((tv, dt), If(c, replace regenv x, replace regenv y, e1, e2), e), regenv'
  | FIf(c, x, y, e1, e2) ->
     let _, dt = dest in
     let tv = Id.gentmp dt in 
     let e1, regenv1 = i dest contfv lcontfv regenv e1 in
     let e2, regenv2 = i dest contfv lcontfv regenv e2 in
     let keys = M.fold (fun k _ s -> S.add k s) regenv2 (M.fold (fun k _ s -> S.add k s) regenv1 S.empty) in
     let e1, e2, e, regenv' = S.fold (fun k (e1, e2, e, regenv) ->
       let t1 = Id.genid k in
       let t2 = Id.genid k in
       match mem k regenv1, mem k regenv2 with
       | true, true ->
	  if replace regenv1 k = replace regenv2 k then
	    e1, e2, e, M.add k (replace regenv1 k) regenv
	  else
	    e1,
	    e2,
	    Let((t2, Type.Int), Union(replace regenv1 k, replace regenv2 k), e),
	    M.add k t2 regenv
       | false, false -> assert false
       | true, false ->
	  e1,
	 (insert dt ((t1, Type.Int), Restore(k)) e2),
	 Let((t2, Type.Int), Union(replace regenv1 k, t1), e),
	 M.add k t2 regenv
       | false, true ->
     	  (insert dt ((t1, Type.Int), Restore(k)) e1),
	 e2,
	 Let((t2, Type.Int), Union(t1, replace regenv2 k), e),
	 M.add k t2 regenv
     ) keys (e1, e2, Ans(Mr(tv)), M.empty) in
     Let((tv, dt), FIf(c, replace regenv x, replace regenv y, e1, e2), e), regenv'
  | IfThen(f, e1) ->
     let _, dt = dest in
     let tv = Id.gentmp dt in 
     let e1, regenv1 = i dest contfv lcontfv regenv e1 in
     let regenv2 = regenv in
     let keys = M.fold (fun k _ s -> S.add k s) regenv2 S.empty in
     let ins, e1, e, regenv' = S.fold (fun k (ins, e1, e, regenv) ->
       let t1 = Id.genid k in
       let t2 = Id.genid k in
       match mem k regenv1 with
       | true ->
	  if replace regenv1 k = replace regenv2 k then
	    ins, e1, e, M.add k (replace regenv1 k) regenv
	  else
	    ins,
	    e1,
	    Let((t2, Type.Int), Union(replace regenv1 k, replace regenv2 k), e),
	    M.add k t2 regenv
       | false ->
	  if not (S.mem k contfv) then
	    ins, e1, e, regenv
	  else if not (S.mem k lcontfv) then
	    ((Id.gentmp Type.Unit, Type.Unit), Save(replace regenv2 k, k))::ins, e1, e, regenv
	  else
	    ins, 
     	    (insert dt ((t1, Type.Int), Restore(k)) e1),
	    Let((t2, Type.Int), Union(t1, replace regenv2 k), e),
	    M.add k t2 regenv
     ) keys ([], e1, Ans(Mr(tv)), M.empty) in
     (List.fold_left (fun e (xt, exp) -> Let(xt, exp, e))
	(Let((tv, dt), IfThen(replace regenv f, e1), e)) ins), regenv'
  | CallCls(l, ys) ->
     i''_call regenv contfv ys (CallCls(l, List.fold_left (fun l y -> l@[replace regenv y]) [] ys)), M.empty
  | CallDir(f, ys) ->
     i''_call regenv contfv ys (CallDir(f, List.fold_left (fun l y -> l@[replace regenv y]) [] ys)), M.empty
  | _ ->
     Ans(replace_exp regenv exp), (
       match exp with
       | CallCls _ | CallDir _ -> assert false
       | If _ | FIf _ | IfThen _ -> assert false
       | _ -> regenv
     )
and i''_call regenv contfv ys exp =
  let e, _ = List.fold_left (fun (e, i) y ->
    Let((regs.(i), Type.Int), Mr(replace regenv y), e), i + 1
  ) (Ans(exp), 0) ys in
  M.fold (fun r r' e ->
    if S.mem r contfv then
      seq(Save(r', r), e)
    else
      e
  ) regenv e

exception RegAlloc_conflict
exception RegAlloc_starvation
    
let j (regmap, pregmap, graph) =
  let vrmap = M.empty in
  (* regmap内で固定レジスタに強制割り当てされているパターンを最優先割り当て *)
  let regmap, vrmap = List.fold_left (fun (regmap, vrmap) (x, y) ->
    match is_reg x, is_reg y with
    | true, true -> assert false
    | true, false -> regmap, M.add y x vrmap
    | false, true -> regmap, M.add x y vrmap
    | false, false -> (x, y)::regmap, vrmap
  ) ([], vrmap) regmap in
  (* 現在の変数レジスタマッピングをベースに、強制割り当てマップより解決できるものは解決する *)
  let map regmap vrmap =
    let rec map_sub regmap vrmap =
      let f, regmap, vrmap = List.fold_left (fun (f, regmap, vrmap) (x, y) ->
	match M.mem x vrmap, M.mem y vrmap with
	| true, true ->
	   if M.find x vrmap <> M.find y vrmap then raise RegAlloc_conflict;
	  f, regmap, vrmap
	| true, false -> false, regmap, M.add y (M.find x vrmap) vrmap
	| false, true -> false, regmap, M.add x (M.find y vrmap) vrmap
	| false, false -> f, (x, y)::regmap, vrmap
      ) (true, [], vrmap) regmap
      in
      if f then
	(regmap, vrmap)
      else
	map_sub regmap vrmap
    in
    map_sub regmap vrmap
  in
  (* 再優先割り当てマップをベースにして、他の強制割り当てが解決できる場合は解決しておく *)
  let regmap, vrmap = map regmap vrmap in
  (* 干渉グラフに抵触していないか調べる *)
  let check vrmap graph = List.fold_left (fun graph (x, y) ->
    try
      if M.find x vrmap = M.find y vrmap then
	raise RegAlloc_conflict
      else
	graph
    with Not_found -> (x, y)::graph
  ) [] graph
  in
  (* 優先割り当てマップの中からレジスタに割り当てられる変数を割り当てる *)
  let regmap, pregmap, graph, vrmap = List.fold_left (fun (regmap, pregmap, graph, vrmap) (x, y) ->
    match is_reg x, is_reg y with
    | true, true -> assert false
    | true, false ->
       let vrmap' = M.add y x vrmap in
       (try
	  let regmap, vrmap = map regmap vrmap' in
	  let graph = check vrmap graph in
	  regmap, pregmap, graph, vrmap
	with RegAlloc_conflict ->
	  regmap, pregmap, graph, vrmap)
    | false, true ->
       let vrmap' = M.add x y vrmap in
       (try
	  let regmap, vrmap = map regmap vrmap' in
	  let graph = check vrmap graph in
	  regmap, pregmap, graph, vrmap
	with RegAlloc_conflict ->
	  regmap, pregmap, graph, vrmap)
    | false, false -> regmap, (x, y)::pregmap, graph, vrmap
  ) (regmap, [], graph, vrmap) pregmap in
  (* 現在の変数レジスタマッピングをベースに、優先割り当てマップよりレジスタに割り当てられる変数は割り当てる *)
  let map' regmap pregmap graph vrmap =
    let rec map_sub regmap pregmap graph vrmap =
      let f, regmap, pregmap, graph, vrmap =
	List.fold_left (fun (f, regmap, pregmap, graph, vrmap) (x, y) ->
	  match M.mem x vrmap, M.mem y vrmap with
	  | true, true -> f, regmap, pregmap, graph, vrmap
	  | true, false ->
	     let vrmap' = M.add y (M.find x vrmap) vrmap in
	     (try
		let regmap, vrmap = map regmap vrmap' in
		let graph = check vrmap graph in
		false, regmap, pregmap, graph, vrmap
	      with RegAlloc_conflict ->
		f, regmap, pregmap, graph, vrmap)
	  | false, true ->
	     let vrmap' = M.add x (M.find y vrmap) vrmap in
	     (try
		let regmap, vrmap = map regmap vrmap' in
		let graph = check vrmap graph in
		false, regmap, pregmap, graph, vrmap
	      with RegAlloc_conflict ->
		f, regmap, pregmap, graph, vrmap)
	  | false, false -> f, regmap, (x, y)::pregmap, graph, vrmap
	) (true, regmap, [], graph, vrmap) pregmap
      in
      if f then
	(regmap, pregmap, graph, vrmap)
      else
	map_sub regmap pregmap graph vrmap
    in
    let regmap, vrmap = map regmap vrmap in
    map_sub regmap pregmap graph vrmap
  in
  (* 優先レジスタ割り当ての結果、他の優先割り当てが割り当てられるなら割り当てる *)
  let regmap, pregmap, graph, vrmap = map' regmap pregmap graph vrmap in
  (* ある変数に対して割り当てられるレジスタを抽出する *)
  let reg_list v vrmap graph =
    assert (not (M.mem v vrmap));
    let invalid = List.fold_left (fun invalid (x, y) ->
      match v = x, v = y with
      | true, true -> assert false
      | true, false -> (try S.add (M.find y vrmap) invalid with Not_found -> invalid)
      | false, true -> (try S.add (M.find x vrmap) invalid with Not_found -> invalid)
      | false, false -> invalid
    ) S.empty graph in
    List.fold_left (fun regs r ->
      if S.mem r invalid then
	regs
      else
	regs@[r]
    ) [] (Array.to_list regs)
  in
  (* 決定できるレジスタは全て割り当てたので、後は制限を満たすように適当に割り当てていく *)
  let rec allocate regmap pregmap graph vrmap =
    let targets = regmap@pregmap@graph in
    if List.length targets = 0 then
      [], [], [], vrmap
    else
      let target, target' = List.hd targets in
      let target = if M.mem target vrmap then target' else target in
      let rec allocate_sub regmap graph vrmap list =
	let reg = try List.hd list with Failure "hd" -> raise RegAlloc_starvation in
	(try
	   let vrmap = M.add target reg vrmap in
	   let regmap, vrmap = map regmap vrmap in
	   let graph = check vrmap graph in
	   regmap, graph, vrmap
	 with RegAlloc_conflict -> allocate_sub regmap graph vrmap (List.tl list))
      in
      let regmap, graph, vrmap = allocate_sub regmap graph vrmap (reg_list target vrmap graph) in
      let regmap, pregmap, graph, vrmap = map' regmap pregmap graph vrmap in
      allocate regmap pregmap graph vrmap
  in
  let _, _, _, vrmap = allocate regmap pregmap graph vrmap in
  vrmap

let rec apply regmap e = try replace_e regmap e with RegNot_found r -> apply (M.add r regs.(0) regmap) e
    
let h { name = Id.L(x); args = ys; body = e; ret = t } = (* 関数のレジスタ割り当て (caml2html: regalloc_h) *)
  let _, e, arg_regs =
    List.fold_left
      (fun (i, e, arg_regs) y ->
       let r = regs.(i) in
       (i + 1,
	Let((y, Type.Int), Mr(regs.(i)), e),
	arg_regs @ [r]
       ))
      (0, e, [])
      ys in
  let a =
    match t with
    | Type.Unit -> Id.gentmp Type.Unit
    | _ -> regs.(0) in
  let e, _ = i (regs.(0), Type.Unit) (fvs (Ans(Nop))) (fvs (Ans(Nop))) M.empty (specify_ret (regs.(0), Type.Unit) e) in
  let map, _ = g (a, t) S.empty (fvs (Ans(Nop))) e in
  let map = j map in
  let e = apply map e in
  { name = Id.L(x); args = arg_regs; body = e; ret = t }

let f (Prog(data, vars, fundefs, e)) = (* プログラム全体のレジスタ割り当て (caml2html: regalloc_f) *)
  show fundefs e;
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)@.";
  let fundefs = List.map h fundefs in
  let e, _ = i (regs.(0), Type.Unit) (fvs (Ans(Nop))) (fvs (Ans(Nop))) M.empty (specify_ret (regs.(0), Type.Unit) e) in
  let map, _ = g (regs.(0), Type.Unit) S.empty (fvs (Ans(Nop))) e in
  let map = j map in
  let e = apply map e in
  show fundefs e;
  let p = Prog(data, vars, fundefs, e) in
  p
