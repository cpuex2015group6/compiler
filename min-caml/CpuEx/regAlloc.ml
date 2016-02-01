open Asm

let showmap f (regmap, pregmap, graph) vrmap =
  Printf.fprintf stdout ">>>> regmap of %s >>>>\n" f;
  Printf.fprintf stdout ">>regmap:\n";
  List.iter (fun (x, y) -> Printf.fprintf stdout "%s %s\n" x y) regmap;
  Printf.fprintf stdout ">>pregmap:\n";
  List.iter (fun (x, y) -> Printf.fprintf stdout "%s %s\n" x y) pregmap;
  Printf.fprintf stdout ">>graph:\n";
  M.iter (fun v s -> S.iter (fun v' -> Printf.fprintf stdout "%s %s\n" v v') s) graph;
  Printf.fprintf stdout ">>vrmap:\n";
  M.iter (fun v r -> Printf.fprintf stdout "%s -> %s\n" v r) vrmap

let rec apply_exp f = function
  | Ans(exp) -> Ans(apply_exp' f exp)
  | Let(xts, exp, e) -> Let(xts, apply_exp' f exp, apply_exp f e)
and apply_exp' f = function
  | If(c, x, y, e1, e2) -> f (If(c, x, y, apply_exp f e1, apply_exp f e2))
  | FIf(c, x, y, e1, e2) -> f (FIf(c, x, y, apply_exp f e1, apply_exp f e2))
  | IfThen(x, e, t) -> f (IfThen(x, apply_exp f e, t))
  | While(x, yts, zs, e) -> f (While(x, yts, zs, apply_exp f e))
  | e -> f e

let rec specify_ret at = function
  | Ans (exp) -> Let(at, exp, Ans(Nop))
  | Let(xts, exp, e) -> Let(xts, exp, specify_ret at e)

let rm_reg l = List.fold_left (fun l v -> if is_reg v then l else l@[v]) [] l
let rm_reg_s s = S.fold (fun v s -> if is_reg v then s else S.add v s) s S.empty
let pair v = List.fold_left (fun graph x -> (x, v)::graph)
let assert_single dest = assert (List.length dest = 1)

let add_graph x y graph =
  let graph =
    if is_reg x then graph
    else
      try
        let s = M.find x graph in
        M.add x (S.add y s) graph
      with Not_found ->
        M.add x (S.singleton y) graph
  in
  if is_reg y then graph
  else
    try
      let s = M.find y graph in
      M.add y (S.add x s) graph
    with Not_found ->
      M.add y (S.singleton x) graph

let union_graph g1 g2 =
  let s1 = M.keys g1 in
  let s2 = M.keys g2 in
  S.fold (fun k graph ->
    let s1 = try M.find k g1 with Not_found -> S.empty in
    let s2 = try M.find k g2 with Not_found -> S.empty in
    M.add k (S.union s1 s2) graph
  ) (S.union s1 s2) M.empty
    
(* 複数の返り値を適切に代入できるよう、相互依存関係を作成 *)
let make_graph graph live contfv dest = function
  | Tuple(xs) ->
     assert (List.length dest = List.length xs);
    let dest = rm_t dest in
    let rec make_graph_sub dest xs live contfv graph =
      if List.length dest = 0 then
	      graph, contfv
      else
	      let contdest = List.tl dest in
	      let dest = List.hd dest in
	      let graph, contfv = make_graph_sub contdest (List.tl xs) (if is_reg dest then live else S.add dest live) contfv graph in
	      let x = List.hd xs in
	      (S.fold (fun v graph -> if S.mem v contfv then add_graph dest v graph else graph) live graph), S.add x contfv
    in
    let graph, _ = make_graph_sub dest xs live contfv graph in
    graph, List.fold_left2 (fun l d x -> (d, x)::l) [] dest xs
  | _ ->
     let dest = rm_t dest in
     let rec make_graph_sub dest live graph =
      if List.length dest = 0 then
	      graph
      else
	      let contdest = List.tl dest in
	      let dest = List.hd dest in
	      let graph = make_graph_sub contdest (if is_reg dest then live else S.add dest live) graph in
	      S.fold (fun v graph -> if S.mem v contfv then add_graph dest v graph else graph) live graph
     in
     make_graph_sub dest live graph, []
  
  
(* 各種マップ生成 *)
let rec g dest live contfv = function
  | Ans exp ->
     let (regmap, pregmap, graph), fv = g' dest live S.empty exp in
     let graph, pregmap' = make_graph graph live contfv dest exp in
     (regmap, pregmap @ pregmap', graph), S.union (rm_reg_s fv) contfv
  | Let(xts, exp, e) ->
     let live' = match exp with
       | CallCls _ | CallDir _ -> S.empty
       | _ -> live
     in
     let (regmap', pregmap', graph') as map, contfv = g dest (S.union (rm_reg_s (rm_t_s xts)) live') contfv e in
     let (regmap, pregmap, graph), fv = (g' xts live contfv exp) in
     let regmap, pregmap, graph = regmap @ regmap', pregmap @ pregmap', union_graph graph graph' in
     let graph, pregmap' = make_graph graph live contfv xts exp in
     (regmap, pregmap @ pregmap', graph), fvs_let (rm_t xts) (rm_reg_s fv) contfv
and g' dest live contfv exp =
  match exp with
  | Nop | Li _ | SetL _ | Add _ | Sub _ | Xor _ | Or _ | And _ | Sll _ | Srl _ | Ldw _ | Stw _ | FAdd _ | FSub _ | FMul _ | FDiv _ | FAbA _ | FAbs _ | Sqrt _ | In | Out _ | GetHp | SetHp _ | Comment _ | Cmp _ | FCmp _ | Save _ | Restore _ ->
     ([], [], M.empty), fvs_exp exp
  | Mr(x) ->
     assert_single dest;
    ([], pair x [] (rm_t dest), M.empty), fvs_exp exp
  | Tuple(xs) ->
     assert (List.length dest = List.length xs);
    ([], List.fold_left2 (fun graph dv x -> (dv, x)::graph) [] (rm_t dest) xs, M.empty), fvs_exp exp
  | CallCls _ | CallDir _ -> (pair regs.(0) [] (rm_t dest), [], M.empty), S.empty
  | Cmpa(_, _, _, w) | FCmpa(_, _, _, w)-> (pair w [] (rm_t dest), [], M.empty), fvs_exp exp
  | While(_, yts, zs, e) ->
     let (regmap, pregmap, graph), contfv' = g dest (S.union (rm_reg_s (rm_t_s yts)) live) contfv (*S.union contfv (fvs_let (rm_t yts) S.empty (fvs e))*) e in
     let graph, pregmap' = make_graph graph live contfv' yts exp in
     ((List.map2 (fun (y, _) z -> (y, z)) yts zs) @ regmap, pregmap @ pregmap', graph), fvs_while yts zs contfv'
  | Continue(_, yts, zs, ws, us) ->
     ((List.map2 (fun w u -> (w, u)) ws us) @ (List.map2 (fun (y, _) z -> (y, z)) yts zs), [], M.empty), fvs_exp exp
  | If(_, x, y, e1, e2) | FIf(_, x, y, e1, e2) ->
     let (regmap1, pregmap1, graph1), contfv1 = g dest live contfv e1 in
     let (regmap2, pregmap2, graph2), contfv2 = g dest live contfv e2 in
     (regmap1@regmap2, pregmap1@pregmap2, union_graph graph1 graph2), fvs_if x y contfv1 contfv2
  | IfThen(f, e, t) ->
     let tmp = List.rev dest in
     let tdest = List.rev (List.tl tmp) in
     assert (List.length tdest = List.length t);
     let (regmap, pregmap, graph), contfv' = g dest live contfv e in
     let regmap = List.fold_left2 (
       fun regmap dv x -> (dv, x)::regmap
     ) regmap (rm_t tdest) t in
     (regmap, pregmap, graph), fvs_ifthen f contfv' t
       
exception RegNot_found of Id.t
    
let replace regenv r = try if is_reg r then r else M.find r regenv with Not_found -> raise (RegNot_found r)
let replace' regenv = function
  | V(x) -> V(replace regenv x)
  | c -> c
let mem r regenv = if is_reg r then true else M.mem r regenv

let rec replace_e regenv = function
  | Ans (exp) -> Ans(replace_exp regenv exp)
  | Let(xts, exp, e) -> Let(List.map (fun (x, t) -> (replace regenv x, t)) xts, replace_exp regenv exp, replace_e regenv e)
and replace_exp regenv = function
  | Nop | Li _ | SetL _ | In | GetHp | Comment _ | Restore _ as exp -> exp
  | Mr(x) -> Mr(replace regenv x)
  | Tuple(xs) -> Tuple(List.fold_left (fun xs x -> xs@[replace regenv x]) [] xs)
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
  | CallCls(l, ys) -> CallCls(l, List.map (fun y -> replace regenv y) ys)
  | CallDir(f, ys) -> CallDir(f, List.map (fun y -> replace regenv y) ys)
  | While(x, yts, zs, e) -> While(x, List.map (fun (y, t) -> (replace regenv y, t)) yts, List.map (fun z -> replace regenv z) zs, replace_e regenv e)
  | Continue(x, yts, zs, ws, us) -> Continue(x, yts, List.map (fun z -> replace regenv z) zs, ws, List.map (fun u -> replace regenv u) us)
  | If(c, x, y, e1, e2) -> If(c, replace regenv x, replace regenv y, replace_e regenv e1, replace_e regenv e2)
  | FIf(c, x, y, e1, e2) -> FIf(c, replace regenv x, replace regenv y, replace_e regenv e1, replace_e regenv e2)
  | IfThen(f, e1, t) -> IfThen(replace regenv f, replace_e regenv e1, List.fold_left (fun l y -> l@[replace regenv y]) [] t)
  | Save(x, y) -> Save(replace regenv x, y)

(* 返り値のTupleの先頭に新しい要素を追加する *)
let rec add_return ts x = function
  | Ans(Tuple(xs)) ->
     assert (List.length xs = List.length ts);
     Ans(Tuple(x::xs))
  | Ans(Mr(y)) ->
     assert_single ts;
     Ans(Tuple([x; y]))
  | Ans(exp) ->
     assert_single ts;
    let t = List.hd ts in
    let tv = Id.gentmp t in
    Let([(tv, t)], exp, Ans(Tuple([x; tv])))
  | Let(yts, exp, e) ->
     Let(yts, exp, add_return ts x e)

let rec add_return_with_restore ts x rx = function
  | Ans(Tuple(xs)) ->
     assert (List.length xs = List.length ts);
     Let([(x, Type.Int)], Restore(rx), Ans(Tuple(x::xs)))
  | Ans(Mr(y)) ->
     assert_single ts;
     Let([(x, Type.Int)], Restore(rx), Ans(Tuple([x; y])))
  | Ans(exp) ->
     assert_single ts;
    let t = List.hd ts in
    let tv = Id.gentmp t in
    Let([(tv, t)], exp, Let([(x, Type.Int)], Restore(rx), Ans(Tuple([x; tv]))))
  | Let(yts, exp, e) ->
     Let(yts, exp, add_return_with_restore ts x rx e)

let cl_vars contfv lcontfv regenv oregenv =
  M.fold (fun r r' (sl, regenv) ->
    if not (S.mem r contfv) then
      (* 使用しない変数はregenvから削除 *)
      sl, M.remove r regenv
    else if not (S.mem r lcontfv) then
      (* Callまでに使用しない変数は退避 *)
      (r', r)::sl, M.remove r regenv
    else
      sl, regenv
  ) oregenv ([], regenv)

type tfv =
  | AnsFv of S.t * S.t * expfv
  | LetFv of S.t * S.t * expfv * tfv
and expfv =
  | GenFv
  | IfFv of tfv * tfv
  | IfThenFv of tfv
  | WhileFv of tfv

let rec makefv dest contfv lcontfv = function
  | Ans(exp) ->
     let expfv = makefv' dest contfv lcontfv exp in
     (concatfvs' (Ans(exp)) dest contfv lcontfv), AnsFv(contfv, lcontfv, expfv)
  | Let(xts, exp, e) ->
     let (contfv, lcontfv), fv = makefv dest contfv lcontfv e in
     let expfv = makefv' dest contfv contfv exp in
     (concatfvs' (Ans(exp)) xts contfv lcontfv), LetFv(contfv, lcontfv, expfv, fv)
and makefv' dest contfv lcontfv exp =
  match exp with
  | If(_, _, _, e1, e2) | FIf(_, _, _, e1, e2) ->
     let _, tfv1 = makefv dest contfv lcontfv e1 in
     let _, tfv2 = makefv dest contfv lcontfv e2 in
     IfFv(tfv1, tfv2)
  | IfThen(_, e, _) ->
     let _, tfv = makefv dest contfv lcontfv e in
     IfThenFv(tfv)
  | While(_, yts, _, e) ->
     let _, tfv = makefv dest contfv lcontfv e in
     WhileFv(tfv)
  | _ ->
     GenFv

(* Save, Restoreの生成 *)
let rec i dest regenv = function
  | AnsFv(contfv, lcontfv, expfv), Ans exp ->
     let oregenv = regenv in
     let e, regenv = i' dest contfv lcontfv regenv (expfv, exp) in
     let sl, regenv = cl_vars contfv lcontfv regenv oregenv in
     let regenv = M.fold (fun r _ regenv -> if S.mem r contfv then regenv else M.remove r regenv) regenv regenv in
     let e = List.fold_left (fun e (r', r) -> seq(Save(r', r), e)) e sl in
     let tmp = List.fold_left (fun tmp t -> tmp@[(Id.gentmp t, t)]) [] (rm_x dest) in
     (* TODO ??? *)
     concat e tmp (List.fold_left (fun e (r', r) -> seq(Save(r', r), e)) (Ans(Tuple(rm_t tmp))) sl), regenv
  | LetFv(contfv, lcontfv, expfv, tfv), Let(xts, exp, e) ->
     let oregenv = regenv in
     let exp, regenv = i' xts contfv lcontfv regenv (expfv, exp) in
     let sl, regenv = cl_vars contfv lcontfv regenv oregenv in
     let e, regenv = i dest (List.fold_left (fun regenv x -> M.add x x regenv) regenv (rm_t xts)) (tfv, e) in       
     List.fold_left (fun e (r', r) -> seq(Save(r', r), e)) (concat exp xts e) sl, regenv
  | _ -> assert false
and i' dest contfv lcontfv regenv ((_, exp) as exp') =
  try i'' dest contfv lcontfv regenv exp' with RegNot_found r ->
    let id = Id.genid r in
    let exp, regenv = i' dest contfv lcontfv (M.add r id regenv) exp' in
    Let([(id, Type.Int)], Restore(r), exp), regenv
and i'' dest contfv lcontfv regenv ((_, exp) as exp') =
  match exp' with
  | IfFv(e1fv, e2fv), If(c, x, y, e1, e2) ->
     let dts = rm_x dest in
     let tvs = List.fold_left (fun tvs dt -> tvs@[Id.gentmp dt]) [] dts in
     let tvs' = tvs in
     let e1, regenv1 = i dest regenv (e1fv, e1) in
     let e2, regenv2 = i dest regenv (e2fv, e2) in
     let keys = M.fold (fun k _ s -> S.add k s) regenv2 (M.fold (fun k _ s -> S.add k s) regenv1 S.empty) in
     let e1, e2, regenv', tvs, dts = S.fold (fun k (e1, e2, regenv, tvs, dts) ->
       let t1 = Id.genid k in
       let t2 = Id.genid k in
       match mem k regenv1, mem k regenv2 with
       | true, true ->
	        if replace regenv1 k = replace regenv2 k then
	          e1, e2, M.add k (replace regenv1 k) regenv, tvs, dts
	        else
	          add_return dts (replace regenv1 k) e1,
	          add_return dts (replace regenv2 k) e2,
	          M.add k t2 regenv,
	          t2::tvs,
	          Type.Int::dts
       | false, false -> assert false
       | true, false ->
	        add_return dts (replace regenv1 k) e1,
	       add_return_with_restore dts t1 k e2,
	       M.add k t2 regenv,
	       t2::tvs,
	       Type.Int::dts
       | false, true ->
	        add_return_with_restore dts t1 k e1,
	       add_return dts (replace regenv2 k) e2,
	       M.add k t2 regenv,
	       t2::tvs,
	       Type.Int::dts
     ) keys (e1, e2, M.empty, tvs, dts) in
     Let((unify_xt tvs dts), If(c, replace regenv x, replace regenv y, e1, e2), Ans(Tuple(tvs'))), regenv'
  | IfFv(e1fv, e2fv), FIf(c, x, y, e1, e2) ->
     let dts = rm_x dest in
     let tvs = List.fold_left (fun tvs dt -> tvs@[Id.gentmp dt]) [] dts in
     let tvs' = tvs in
     let e1, regenv1 = i dest regenv (e1fv, e1) in
     let e2, regenv2 = i dest regenv (e2fv, e2) in
     let keys = M.fold (fun k _ s -> S.add k s) regenv2 (M.fold (fun k _ s -> S.add k s) regenv1 S.empty) in
     let e1, e2, regenv', tvs, dts = S.fold (fun k (e1, e2, regenv, tvs, dts) ->
       let t1 = Id.genid k in
       let t2 = Id.genid k in
       match mem k regenv1, mem k regenv2 with
       | true, true ->
	        if replace regenv1 k = replace regenv2 k then
	          e1, e2, M.add k (replace regenv1 k) regenv, tvs, dts
	        else
	          add_return dts (replace regenv1 k) e1,
	          add_return dts (replace regenv2 k) e2,
	          M.add k t2 regenv,
	          t2::tvs,
	          Type.Int::dts
       | false, false -> assert false
       | true, false ->
	        add_return dts (replace regenv1 k) e1,
	       add_return_with_restore dts t1 k e2,
	       M.add k t2 regenv,
	       t2::tvs,
	       Type.Int::dts
       | false, true ->
	        add_return_with_restore dts t1 k e1,
	       add_return dts (replace regenv2 k) e2,
	       M.add k t2 regenv,
	       t2::tvs,
	       Type.Int::dts
     ) keys (e1, e2, M.empty, tvs, dts) in
     Let((unify_xt tvs dts), FIf(c, replace regenv x, replace regenv y, e1, e2), Ans(Tuple(tvs'))), regenv'
  | IfThenFv(efv), IfThen(f, e1, t) ->
     let dts = rm_x dest in
     let tvs = List.fold_left (fun tvs dt -> tvs@[Id.gentmp dt]) [] dts in
     let tvs' = tvs in
     let e1, regenv1 = i dest regenv (efv, e1) in
     let regenv2 = regenv in
     let keys = M.fold (fun k _ s -> S.add k s) regenv2 (M.fold (fun k _ s -> S.add k s) regenv1 S.empty) in
     let ins, e1, t, regenv', tvs, dts = S.fold (fun k (ins, e1, t, regenv, tvs, dts) ->
       let t1 = Id.genid k in
       let t2 = Id.genid k in
       match mem k regenv1 with
       | true ->
	        if replace regenv1 k = replace regenv2 k then
	          ins, e1, t, M.add k (replace regenv1 k) regenv, tvs, dts
	        else
	          ins,
	          add_return dts (replace regenv1 k) e1,
	          (replace regenv2 k)::t,
	          M.add k t2 regenv,
	          t2::tvs,
	          Type.Int::dts
       | false ->
	        if not (S.mem k contfv) then
	          ins, e1, t, regenv, tvs, dts
	        else if not (S.mem k lcontfv) then
	          ([(Id.gentmp Type.Unit, Type.Unit)], Save(replace regenv2 k, k))::ins, e1, t, regenv, tvs, dts
	        else
	          ins,
	          add_return_with_restore dts t1 k e1,
	          (replace regenv2 k)::t,
	          M.add k t2 regenv,
	          t2::tvs,
	          Type.Int::dts
     ) keys ([], e1, t, M.empty, tvs, dts) in
     (List.fold_left (fun e (xts, exp) -> Let(xts, exp, e))
	      (Let((unify_xt tvs dts), IfThen(replace regenv f, e1, t), Ans(Tuple(tvs')))) ins), regenv'
  | WhileFv(efv), While(x, yts, zs, e) ->
     let e = apply_exp (fun exp -> match exp with | Continue(x, yts, zs, ws, us) -> Continue(x, yts, zs, List.map (fun w -> replace regenv w) ws, us) | _ -> exp) e in
     let regenv = (List.fold_left (fun regenv (y, _) -> M.add y y regenv) regenv yts) in
     let e, regenv' = i dest regenv (efv, e) in
     Ans(While(x, List.map (fun (y, t) -> replace regenv y, t) yts, List.map (fun z -> replace regenv z) zs, e)), regenv'
  | GenFv, CallCls(l, ys) ->
     i''_call regenv contfv ys (CallCls(l, List.fold_left (fun l y -> l@[replace regenv y]) [] ys)), M.empty
  | GenFv, CallDir(f, ys) ->
     i''_call regenv contfv ys (CallDir(f, List.fold_left (fun l y -> l@[replace regenv y]) [] ys)), M.empty
  | GenFv, _ ->
     Ans(replace_exp regenv exp), (
       match exp with
       | CallCls _ | CallDir _ -> assert false
       | If _ | FIf _ | IfThen _ -> assert false
       | While _ -> assert false
       | _ -> regenv
     )
  | _ -> assert false
and i''_call regenv contfv ys exp =
  let tv = Id.genid "t" in
  let e, _ = List.fold_left (fun (e, i) y ->
    Let([(regs.(i), Type.Int)], Mr(replace regenv y), e), i + 1
  ) (Let([(tv, Type.Int)], exp, Ans(Mr(tv))), 0) ys in
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
    | true, true -> assert (x = y); regmap, vrmap
    | true, false ->
       (try
	  if M.find y vrmap <> x then
	    raise RegAlloc_conflict
	  else
	    regmap, vrmap
	with Not_found ->
	  regmap, M.add y x vrmap)
    | false, true ->
       (try
	  if M.find x vrmap <> y then
	    raise RegAlloc_conflict
	  else
	    regmap, vrmap
	with Not_found ->
	  regmap, M.add x y vrmap)
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
  let oregmap = regmap in
  (* xが干渉グラフに抵触していないか調べる *)
  let check x vrmap graph =
    let rec check_sub1 x checked =
      let check_sub2 x = 
        assert (M.mem x vrmap);
        try
          let x' = M.find x vrmap in
          S.iter (fun y ->
                  try
                    if x' = (if is_reg y then y else M.find y vrmap) then
                      raise RegAlloc_conflict
                  with Not_found -> ()
                 ) (M.find x graph)
        with Not_found -> ()
      in
      check_sub2 x;
      List.iter (fun (y, z) ->
                 match x = y, x = z with
                 | true, false ->
                    if not (S.mem z checked) then check_sub1 z (S.add x checked);
                 | false, true ->
                    if not (S.mem y checked) then check_sub1 y (S.add x checked);
                 | _ -> ()
                ) oregmap;
    in
    check_sub1 x S.empty;
    graph
  in
  (* 優先割り当てマップの中からレジスタに割り当てられる変数を割り当てる *)
  let regmap, pregmap, graph, vrmap = List.fold_left (fun (regmap, pregmap, graph, vrmap) (x, y) ->
    match is_reg x, is_reg y with
    | true, true -> assert false
    | true, false ->
       if M.mem y vrmap then
	       regmap, pregmap, graph, vrmap
       else
	       let vrmap' = M.add y x vrmap in
	       (try
	          let regmap, vrmap = map regmap vrmap' in
	          let graph = check y vrmap graph in
	          regmap, pregmap, graph, vrmap
	        with RegAlloc_conflict ->
	          regmap, pregmap, graph, vrmap)
    | false, true ->
       if M.mem x vrmap then
	       regmap, pregmap, graph, vrmap
       else
	       let vrmap' = M.add x y vrmap in
	       (try
	          let regmap, vrmap = map regmap vrmap' in
	          let graph = check x vrmap graph in
	          regmap, pregmap, graph, vrmap
	        with RegAlloc_conflict ->
	          regmap, pregmap, graph, vrmap)
    | false, false -> regmap, (x, y)::pregmap, graph, vrmap
  ) (regmap, [], graph, vrmap) pregmap in
  (* 現在の変数レジスタマッピングをベースに、優先割り当てマップよりレジスタに割り当てられる変数は割り当てる *)
  let map' regmap pregmap graph vrmap =
    let rec map_sub regmap pregmap graph vrmap =
      let plist, pregmap =
	      List.fold_left (fun (l, pregmap) (x, y) ->
	        match M.mem x vrmap, M.mem y vrmap with
	        | true, true -> l, pregmap
	        | true, false -> (y, x)::l, pregmap
	        | false, true -> (x, y)::l, pregmap
	        | false, false -> l, (x, y)::pregmap
	      ) ([], []) pregmap
      in
      (* 優先割り当てを実際に試す。ダメなら再試行 *)
      let rec try_map regmap graph vrmap plist =
        if List.length plist = 0 then
          true, regmap, graph, vrmap
        else
      	  (try
             let vrmap =
               List.fold_left (fun vrmap (x, y) ->
                 M.add x (M.find y vrmap) vrmap
               ) vrmap plist
             in
		         let regmap, vrmap = map regmap vrmap in
             let graph =
               List.fold_left (fun graph (x, _) ->
                 check x vrmap graph
               ) graph plist
             in
		         false, regmap, graph, vrmap
	         with RegAlloc_conflict ->
             if List.length plist = 1 then
               true, regmap, graph, vrmap
             else
               let _, plist1, plist2 = List.fold_left (fun (x, plist1, plist2) ele ->
                 if x = 0 then
                   0, plist1, ele::plist2
                 else
                   (x - 1), ele::plist1, plist2
               ) (((List.length plist) / 2), [], []) plist
               in
               let f1, regmap, graph, vrmap = try_map regmap graph vrmap plist1 in
               let f2, regmap, graph, vrmap = try_map regmap graph vrmap plist2 in
		           f1 && f2, regmap, graph, vrmap)
      in
      let f, regmap, graph, vrmap = try_map regmap graph vrmap plist in
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
    let invalid =
      try
        S.fold (fun x invalid ->
          try S.add (if is_reg x then x else M.find x vrmap) invalid
          with Not_found -> invalid
        ) (M.find v graph) S.empty
      with Not_found -> S.empty
    in
    List.fold_left (fun regs r ->
      if S.mem r invalid then
	      regs
      else
	      regs@[r]
    ) [] (Array.to_list regs)
  in
  (* 決定できるレジスタは全て割り当てたので、後は制限を満たすように適当に割り当てていく *)
  let rec allocate f regmap pregmap graph vrmap =
    let rec allocate' f targets regmap pregmap graph vrmap =
      if List.length targets = 0 then
        vrmap
      else
        let target = List.hd targets in
        let targets = List.tl targets in
        if M.mem target vrmap then
          allocate' f targets regmap pregmap graph vrmap
        else
          let _ = assert (not (is_reg target)) in
          let rec allocate_sub regmap graph vrmap list =
	          let reg = try List.hd list with Failure "hd" -> raise RegAlloc_starvation in
	          (try
	             let vrmap = M.add target reg vrmap in
	             let regmap, vrmap = map regmap vrmap in
               let graph = if f then check target vrmap graph else graph in
	             regmap, graph, vrmap
	           with RegAlloc_conflict -> allocate_sub regmap graph vrmap (List.tl list))
          in
          let regmap, graph, vrmap = allocate_sub regmap graph vrmap (reg_list target vrmap graph) in
          let regmap, pregmap, graph, vrmap = map' regmap pregmap graph vrmap in
          allocate' f targets regmap pregmap graph vrmap
    in
    let get_targets l = S.elements (List.fold_left (fun s (x, y) ->
      let s = if is_reg x then s else S.add x s in
      if is_reg y then s else S.add y s
    ) S.empty l) in
    let vrmap = allocate' f (get_targets regmap) regmap pregmap graph vrmap in
    let vrmap = allocate' f (get_targets pregmap) regmap pregmap graph vrmap in
    let vrmap = allocate' f (S.elements (M.keys graph)) regmap pregmap graph vrmap in
    vrmap
  in
  let vrmap' = allocate false regmap pregmap graph vrmap in
  let vrmap =
    try
      let _ = M.iter (fun k _ -> let _ = check k vrmap' graph in ()) graph  in
      vrmap'
    with RegAlloc_conflict ->
      (
        let vrmap = allocate true regmap pregmap graph vrmap in
        let _ = M.iter (fun k _ -> let _ = check k vrmap graph in ()) graph in
        vrmap
      )
  in
  vrmap

(* 二重Saveの除去 *)
let rec l env = function
  | Ans(Save(_, y)) when S.mem y env -> Ans(Nop)
  | Ans(exp) -> Ans(l' env exp)
  | Let(xts, Save(_, y), e) when S.mem y env -> l env e
  | Let(xts, Save(x, y), e) -> Let(xts, Save(x, y), l (S.add y env) e)
  | Let(xts, exp, e) -> Let(xts, l' env exp, l env e)
and l' env = function
  | If(c, x, y, e1, e2) ->
     let e1 = l env e1 in
     let e2 = l env e2 in
     If(c, x, y, e1, e2)
  | FIf(c, x, y, e1, e2) ->
     let e1 = l env e1 in
     let e2 = l env e2 in
     FIf(c, x, y, e1, e2)
  | IfThen(f, e, t) ->
     let e = l env e in
     IfThen(f, e, t)
  | While(x, yts, zs, e) ->
     let e = l env e in
     While(x, yts, zs, e)
  | _ as exp -> exp
                             
let rec replace_reg regmap e = try replace_e regmap e with RegNot_found r -> replace_reg (M.add r regs.(0) regmap) e

let k dest e =
  let _, tfv = makefv [(regs.(0), Type.Unit)] (fvs (Ans(Nop))) (fvs (Ans(Nop))) e in
  let e, _ = i [(regs.(0), Type.Unit)] M.empty (tfv, e) in
  show [] e;
  let e = l S.empty e in
  let map, _ = g [dest] S.empty (fvs (Ans(Nop))) e in
  let vrmap = j map in
  let e = replace_reg vrmap e in
  e
  
let h { name = Id.L(x); args = ys; body = e; ret = t } = (* 関数のレジスタ割り当て (caml2html: regalloc_h) *)
  let _, e, arg_regs =
    List.fold_left
      (fun (i, e, arg_regs) y ->
       let r = regs.(i) in
       (i + 1,
	      Let([(y, Type.Int)], Mr(regs.(i)), e),
	      arg_regs @ [r]
      ))
      (0, e, [])
      ys in
  let a =
    match t with
    | Type.Unit -> Id.gentmp Type.Unit
    | _ -> regs.(0) in
  let e = specify_ret [(regs.(0), Type.Unit)] e in
  let e = k (a, t) e in
  { name = Id.L(x); args = arg_regs; body = e; ret = t }

let f (Prog(data, vars, fundefs, e)) = (* プログラム全体のレジスタ割り当て (caml2html: regalloc_f) *)
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)@.";
  show fundefs e;
  let fundefs = List.map h fundefs in
  let e = specify_ret [(regs.(0), Type.Unit)] e in
  let e = k (regs.(0), Type.Unit) e in
  let p = Prog(data, vars, fundefs, e) in
  p
