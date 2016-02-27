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
  | Ans(exp) -> apply_exp' f exp
  | Let(xts, exp, e) -> concat (apply_exp' f exp) xts (apply_exp f e)
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
(* TODO もうちょっとなんとかならないか *)
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
     let (regmap, pregmap, graph), fv = g' dest live contfv exp in
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
     let (regmap, pregmap, graph), contfv' = g dest (S.union (rm_reg_s (rm_t_s yts)) live) contfv e in
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
    
let replace regenv r = try if is_reg r then r else fst (M.find r regenv) with Not_found -> raise (RegNot_found r)

let replace' regenv = function
  | V(x) -> V(replace regenv x)
  | c -> c
let get_sreg regenv r = try if is_reg r then assert false else snd (M.find r regenv) with Not_found -> raise (RegNot_found r)
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

let save_vars contfv lcontfv regenv sregenv oregenv =
  M.fold (fun r (r', sr) (sl, regenv, sregenv) ->
    if not (S.mem r contfv) then
      (* 使用しない変数はregenvから削除 *)
      sl, M.remove r regenv, M.remove r sregenv
    else if not (S.mem r lcontfv) then
      (* Callまでに使用しない変数は退避 *)
      (r', sr)::sl, M.remove r regenv, M.add r sr sregenv
    else
      sl, regenv, sregenv
  ) oregenv ([], regenv, sregenv)

let clean_vars contfv lcontfv regenv sregenv =
  M.fold (fun r (r', sr) (regenv, sregenv) ->
    if not (S.mem r contfv) then
      M.remove r regenv, M.remove r sregenv
    else if not (S.mem r lcontfv) then
      M.remove r regenv, M.add r sr sregenv
    else
      regenv, sregenv
  ) regenv (regenv, sregenv)
    
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

let mfind x map = if M.mem x map then M.find x map else assert false

let i_solve_conflict cvars regenv sregenv exp =
  (* TODO 既にSave済み変数があれば、そちらに回す *)
  let rvs = 
    if S.is_empty cvars then
      []
    else
      let vars = S.filter (fun v -> M.mem v regenv) cvars in
      if S.is_empty vars then
        []
      else
            (* 全変数の探索(letによる除去も行わない) *)
        let rec scan = function
          | Ans(exp) -> scan' exp
          | Let(_, exp, e) -> S.union (scan' exp) (scan e)
        and scan' = function
          | If(_, x, y, e1, e2) | FIf(_, x, y, e1, e2) -> S.add x (S.add y (S.union (scan e1) (scan e2)))
          | IfThen(x, e, t) -> S.add x (S.union (scan e) (S.of_list t))
          | While(_, yts, zs, e) -> S.union (S.of_list zs) (scan e)
          | exp -> fvs_exp exp
        in
        match exp with
        | While(_)
        | If(_) | FIf(_) ->
           let fv = scan' exp in
           let sfvs = S.filter (fun x -> not (S.mem x fv)) vars in
           if sfvs = vars then
                 (* 関係ないのでスルー *)
             []
           else
             if S.is_empty sfvs then
               (* While内部での退避を期待 *)
               []
             else
               (* 退避 *)
               [S.choose sfvs]
        | _ -> []
  in
  let oregenv = regenv in
  let regenv, sregenv = List.fold_left (fun (regenv, sregenv) r ->
    let sr = get_sreg oregenv r in
    M.remove r regenv, M.add r sr sregenv
  ) (regenv, sregenv) rvs in
  let cvars = List.fold_left (fun cvars rv -> if S.mem rv cvars then S.empty else cvars) cvars rvs in
  let rvs = List.map (fun r -> replace oregenv r, get_sreg oregenv r) rvs in
  rvs, cvars, regenv, sregenv
    
(* Save, Restoreの生成 *)
let rec i dest regenv sregenv cvars = function
  | AnsFv(contfv, lcontfv, expfv), Ans exp ->
     let rvs, cvars, regenv, sregenv  = i_solve_conflict cvars regenv sregenv exp in
     let oregenv = regenv in
     let e, cvars, regenv, sregenv = i' dest contfv lcontfv regenv sregenv cvars (expfv, exp) in
     let sl, regenv, sregenv = save_vars contfv lcontfv regenv sregenv oregenv in
     let sl = sl @ rvs in
     let regenv, sregenv = clean_vars contfv lcontfv regenv sregenv in
     let e = 
       if List.length sl = 0 then
         e
       else
         let e = List.fold_left (fun e (r', r) -> seq(Save(r', r), e)) e sl in
         let tmp = List.fold_left (fun tmp t -> tmp@[(Id.gentmp t, t)]) [] (rm_x dest) in
         concat e tmp (Ans(Tuple(rm_t tmp)))
     in
     e, cvars, regenv, sregenv
  | LetFv(contfv, lcontfv, expfv, tfv), Let(xts, exp, e) ->
     let rvs, cvars, regenv, sregenv = i_solve_conflict cvars regenv sregenv exp in
     let oregenv = regenv in
     let exp, cvars, regenv, sregenv = i' xts contfv lcontfv regenv sregenv cvars (expfv, exp) in
     let sl, regenv, sregenv = save_vars contfv lcontfv regenv sregenv oregenv in
     let sl = sl @ rvs in
     let e, cvars, regenv, sregenv = i dest regenv sregenv cvars (tfv, e) in       
     List.fold_left (fun e (r', r) -> seq(Save(r', r), e)) (concat exp xts e) sl, cvars, regenv, sregenv
  | _ -> assert false
and i' dest contfv lcontfv regenv sregenv cvars ((_, exp) as exp') =
  try
    i'' dest contfv lcontfv regenv sregenv cvars exp'
  with RegNot_found r ->
    let id = Id.genid r in
    let sr =
      try
        M.find r sregenv
      with Not_found ->
        assert false
    in
    let sregenv = M.remove r sregenv in
    let exp, cvars, regenv, sregenv = i' dest contfv lcontfv (M.add r (id, sr) regenv) sregenv cvars exp' in
    Let([(id, Type.Int)], Restore(sr), exp), cvars,  regenv, sregenv
and i'' dest contfv lcontfv regenv sregenv cvars ((_, exp) as exp') =
  match exp' with
  | IfFv(e1fv, e2fv), If(c, x, y, e1, e2)
  | IfFv(e1fv, e2fv), FIf(c, x, y, e1, e2) ->
     let dts = rm_x dest in
     let tvs = List.map (fun dt -> Id.gentmp dt) dts in
     let tvs' = tvs in
     let x = replace regenv x in
     let y = replace regenv y in
     let oregenv = regenv in
     let e1, cvars1, regenv1, sregenv1 = i dest regenv sregenv cvars (e1fv, e1) in
     let e2, cvars2, regenv2, sregenv2 = i dest regenv sregenv cvars (e2fv, e2) in
     let cvars = if cvars1 <> cvars || cvars2 <> cvars then
         S.empty
       else
         cvars
     in
     let keys = S.union (M.keys regenv2) (M.keys regenv1) in
     let keys = List.fold_left (fun keys (d, _) -> S.remove d keys) keys dest in
     let e1, e2, regenv, tvs, dts = S.fold (fun k (e1, e2, regenv, tvs, dts) ->
       let t1 = Id.genid k in
       let t2 = Id.genid k in
       match mem k regenv1, mem k regenv2 with
       | true, true ->
          assert (not (M.mem k sregenv1));
         assert (not (M.mem k sregenv2));
         let sk' = if mem k oregenv then get_sreg oregenv k else k in
         let sk = if get_sreg regenv1 k = get_sreg regenv2 k then get_sreg regenv1 k else sk' in
	       if replace regenv1 k = replace regenv2 k then
           let k' = replace regenv1 k in
	         e1, e2, M.add k (k', sk) regenv, tvs, dts
	       else
	         add_return dts (replace regenv1 k) e1,
	         add_return dts (replace regenv2 k) e2,
	         M.add k (t2, sk) regenv,
	         t2::tvs,
	         Type.Int::dts
       | false, false -> assert false
       | true, false ->
          assert (not (M.mem k sregenv1));
         assert (M.mem k sregenv2);
         let sk = M.find k sregenv2 in
	       add_return dts (replace regenv1 k) e1,
	       add_return_with_restore dts t1 sk e2,
	       M.add k (t2, sk) regenv,
	       t2::tvs,
	       Type.Int::dts
       | false, true ->
          assert (M.mem k sregenv1);
          assert (not (M.mem k sregenv2));
          let sk = M.find k sregenv1 in
	        add_return_with_restore dts t1 sk e1,
	        add_return dts (replace regenv2 k) e2,
	        M.add k (t2, sk) regenv,
	        t2::tvs,
	        Type.Int::dts
     ) keys (e1, e2, M.empty, tvs, dts) in
     (* If文内を通過する変数が原因でコンフリクトが発生する場合、まずはIf内部で死ぬようにする *)
     let rec kill' = function
       | Let(xts, exp, e) ->
          let e, svs = kill' e in
          Let(xts, exp, e), svs
       | Ans(Tuple(xs)) ->
         let x's, xs = List.fold_left (fun (x's, xs) x ->
           if S.mem x cvars && M.mem x oregenv then
             let x' = Id.genid x in
             (x', x)::x's, xs@[x']
           else
             x's, xs@[x]
         ) ([], []) xs in
         List.fold_left (fun e (x', x) ->
           Let([(x', Type.Int)], Restore(get_sreg oregenv x), e)
         ) (Ans(Tuple(xs))) x's, List.map (fun (_, x) -> x) x's
       | Ans(Mr(x)) as e ->
         if S.mem x cvars && M.mem x oregenv then
           let x' = Id.genid x in
           Let([(x', Type.Int)], Restore(get_sreg oregenv x), Ans(Mr(x'))), [x]
         else
           e, []
       | Ans(exp) as e ->
          e, []
     in
     let kill e =
       let e, svs = kill' e in
       List.fold_left (fun e sv -> seq(Save(sv, get_sreg oregenv sv), e)) e svs
     in
     let e1 = kill e1 in
     let e2 = kill e2 in
     (* 次に、末尾で同じ変数からRestoreをしている場合は除去する *)
     let rec get_tail regenv = function
       | Let([(x, t)], Restore(x'), e) -> get_tail (M.add x x' regenv) e
       | Let(_, _, e) -> get_tail regenv e
       | Ans(Tuple(xs)) -> regenv, Some(xs)
       | Ans(Mr(x)) -> regenv, Some([x])
       | Ans(_) -> regenv, None
     in
     let rregenv1, e1t = get_tail M.empty e1 in
     let rregenv2, e2t = get_tail M.empty e2 in
     let tvs, dts, rvs, cvars, e1, e2 = match e1t, e2t with
       | Some(e1t), Some(e2t) ->
          assert ((List.length tvs = List.length e1t) && (List.length e1t = List.length e2t));
         let rec fold_left4 f a l1 l2 l3 l4 =
           match l1, l2, l3, l4 with
           | [], [], [], [] -> a
           | x1::l1', x2::l2', x3::l3', x4::l4' -> fold_left4 f (f a x1 x2 x3 x4) l1' l2' l3' l4'
           | _ -> assert false
         in
         let tvs, dts, rvs, cvars, e1t, e2t =
           fold_left4 (fun (tvs, dts, rvs, cvars, e1t, e2t) tv dt t1 t2 ->
           try 
             if M.find t1 rregenv1  = M.find t2 rregenv2 then
               (tvs, dts, ((tv, dt), M.find t1 rregenv1)::rvs,
                (if S.mem t1 cvars || S.mem t2 cvars then S.empty else cvars), e1t, e2t)
             else
               (tvs@[tv], dts@[dt], rvs, cvars, e1t@[t1], e2t@[t2])
           with Not_found ->
             tvs@[tv], dts@[dt], rvs, cvars, e1t@[t1], e2t@[t2]
           ) ([], [], [], cvars, [], []) tvs dts e1t e2t
         in
         let rec replace_tail xs = function
           | Let(xts, exp, e) -> Let(xts, exp, replace_tail xs e)
           | Ans(Tuple(_)) -> Ans(Tuple(xs))
           | Ans(Mr(_)) -> Ans(Tuple(xs))
           | Ans(_) -> assert false
         in
         tvs, dts, rvs, cvars, replace_tail e1t e1, replace_tail e2t e2
       | _ ->
          tvs, dts, [], cvars, e1, e2
     in
     let exp = match exp' with
       | _, If(_) -> If(c, x, y, e1, e2)
       | _, FIf(_) -> FIf(c, x, y, e1, e2)
       | _ -> assert false
     in
     let regenv = List.fold_left (fun regenv (k, _) ->
       if is_reg k then
         regenv
       else
         (
           assert (M.mem k regenv1 = M.mem k regenv2);
           if M.mem k regenv1 then
             (
               assert (replace regenv1 k = k);
               assert (replace regenv2 k = k);
               let sk' = k in
               let sk = if get_sreg regenv1 k = get_sreg regenv2 k then get_sreg regenv1 k else sk' in
	             M.add k (k, sk) regenv
             )
           else
             regenv
         )
     ) regenv dest in
     let sregenv = S.fold (fun k sregenv -> assert (M.find k sregenv1 = M.find k sregenv2); M.add k (M.find k sregenv1) sregenv) (S.inter (M.keys sregenv1) (M.keys sregenv2)) M.empty in
     (if List.length tvs = List.length tvs' &&
        List.fold_left2 (fun f tv tv' -> f && (tv = tv')) true tvs tvs' &&
        List.length rvs = 0 then
         Ans(exp)
      else
         Let((unify_xt tvs dts), exp, List.fold_left (fun e (rxt, rv) -> Let([rxt], Restore(rv), e)) (Ans(Tuple(tvs'))) rvs)
     ), cvars, regenv, sregenv
  | IfThenFv(efv), IfThen(x, e1, t) ->
     assert false;
  | WhileFv(efv), While(x, yts, zs, e) ->
     let dts = rm_x dest in
     let tvs = List.fold_left (fun tvs dt -> tvs@[Id.gentmp dt]) [] dts in
     let tvs' = tvs in
     let zs = List.map (fun z -> replace regenv z) zs in
     let e = apply_exp (fun exp -> match exp with | Continue(x', yts, zs, ws, us) when x = x' -> Ans(Continue(x, yts, zs, List.map (fun w -> replace regenv w) ws, us)) | _ -> Ans(exp)) e in
     let regenv = (List.fold_left (fun regenv (y, _) -> M.add y (y, y) regenv) regenv yts) in
     let e, cvars, regenv, sregenv = i dest regenv sregenv cvars (efv, e) in
     let e, regenv, tvs, dts = M.fold (fun k (k', sk) (e, regenv, tvs, dts) ->
       if List.mem k (rm_t dest) then
         e, regenv, tvs, dts
       else
         let t = Id.genid k in
         add_return dts k' (apply_exp (fun exp -> match exp with | Continue (x', yts, zs, ws, us) when x = x' -> Ans(Continue(x, yts, zs, k'::ws, k'::us)) | _ -> Ans(exp)) e),
         M.add k (t, sk) regenv,
         t::tvs,
         Type.Int::dts
     ) regenv (e, regenv, tvs, dts) in
     let exp = While(x, yts, zs, e) in
     let exp =
       if List.length tvs = List.length tvs' then
         Ans(exp)
       else
         Let((unify_xt tvs dts), exp, Ans(Tuple(tvs')))
     in
     exp, cvars, regenv, sregenv
  | GenFv, CallCls(l, ys) ->
     let e, sregenv = i''_call regenv sregenv contfv ys (CallCls(l, List.fold_left (fun l y -> l@[replace regenv y]) [] ys)) in
     e, cvars, List.fold_left (fun regenv (d, _) -> if is_reg d then regenv else M.add d (d, d) regenv) M.empty dest, sregenv
  | GenFv, CallDir(f, ys) ->
     let e, sregenv = i''_call regenv sregenv contfv ys (CallDir(f, List.fold_left (fun l y -> l@[replace regenv y]) [] ys)) in
     e, cvars, List.fold_left (fun regenv (d, _) -> if is_reg d then regenv else M.add d (d, d) regenv) M.empty dest, sregenv
  | GenFv, _ ->
     Ans(match exp with
     | Save(r, _) when not (M.mem r regenv) -> Nop
     | _ -> replace_exp regenv exp), cvars, (
       match exp with
       | CallCls _ | CallDir _ -> assert false
       | If _ | FIf _ | IfThen _ -> assert false
       | While _ -> assert false
       | Restore(r) ->
          assert_single dest;
         let d = fst (List.hd dest) in
         M.add d (d, r) regenv
       | Save(r, r') ->
          if M.mem r regenv then
            assert (get_sreg regenv r = r')
          else
            assert (M.mem r sregenv && r' = M.find r sregenv);
          regenv
       | Mr(r) ->
          assert_single dest;
         let d = fst (List.hd dest) in
         if is_reg d then
           regenv
         else
           M.add d (d, if is_reg r then d else get_sreg regenv r) regenv
       | Tuple(rs) ->
          assert (List.length dest = List.length rs);
         List.fold_left2 (fun regenv (d, _) r ->
           if is_reg d then
             regenv
           else
             M.add d (d, if is_reg r then d else get_sreg regenv r) regenv
         ) regenv dest rs
       | _ -> List.fold_left (fun regenv (d, _) ->
         if is_reg d then
           regenv
         else
           M.add d (d, d) regenv
       ) regenv dest
     ), sregenv
  | _ -> assert false
and i''_call regenv sregenv contfv ys exp =
  let tv = Id.genid "t" in
  let e, _ = List.fold_left (fun (e, i) y ->
    Let([(regs.(i), Type.Int)], Mr(replace regenv y), e), i + 1
  ) (Let([(tv, Type.Int)], exp, Ans(Mr(tv))), 0) ys in
  M.fold (fun r (r', sr) (e, sregenv) ->
    if S.mem r contfv then
      (seq(Save(r', sr), e), M.add r sr sregenv)
    else
      (e, sregenv)
  ) regenv (e, sregenv)

exception RegAlloc_conflict
exception RegAlloc_starvation of Id.t
    
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
	          let reg = try List.hd list with Failure "hd" -> raise (RegAlloc_starvation target) in
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
     
let rec replace_reg regmap e =
  try replace_e regmap e with
  | RegNot_found r -> replace_reg (M.add r (regs.(0), "") regmap) e

(* restoreされた変数を実際に使う場所まで動かす *)
let rec move_restore vars regenv = function
  | Let(xts, Restore(sx), e) ->
     assert_single xts;
    let (x, t) = List.hd xts in
    move_restore vars (M.add x sx regenv) e
  | Let(xts, exp, e) ->
     let rvs, regenv = S.fold (fun fv (rvs, regenv) ->
       if M.mem fv regenv then
         (fv, M.find fv regenv)::rvs, M.remove fv regenv
       else
         rvs, regenv
     ) (fvs_exp exp) ([], regenv)
     in
     let vars = M.fold (fun k _ vars -> if S.mem k vars then S.empty else vars) regenv vars in
     let exp, vars = move_restore' vars exp in
     let e, vars = move_restore vars regenv e in
     List.fold_left (fun e (x, sx) ->
       Let([(x, Type.Int)], Restore(sx), e)
     ) (Let(xts, exp, e)) rvs, vars
  | Ans(exp) ->
     let rvs, regenv = S.fold (fun fv (rvs, regenv) ->
       if M.mem fv regenv then
         (fv, M.find fv regenv)::rvs, M.remove fv regenv
       else
         rvs, regenv
     ) (fvs_exp exp) ([], regenv)
     in
     let vars = M.fold (fun k _ vars -> if S.mem k vars then S.empty else vars) regenv vars in
     let exp, vars = move_restore' vars exp in
     List.fold_left (fun e (x, sx) ->
       Let([(x, Type.Int)], Restore(sx), e)
     ) (Ans(exp)) rvs, vars
and move_restore' vars = function
  | If(c, x, y, e1, e2) ->
     let e1, vars1 = move_restore vars M.empty e1 in
     let e2, vars2 = move_restore vars M.empty e2 in
     If(c, x, y, e1, e2), S.inter vars1 vars2
  | FIf(c, x, y, e1, e2) ->
     let e1, vars1 = move_restore vars M.empty e1 in
     let e2, vars2 = move_restore vars M.empty e2 in
     FIf(c, x, y, e1, e2), S.inter vars1 vars2
  | While(x, yts, zs, e) ->
     let e, vars = move_restore vars M.empty e in
     While(x, yts, zs, e), vars
  | IfThen(_) -> assert false
  | _ as exp -> exp, vars
       
let rec k' dest live e =
  S.iter (fun x -> prerr_endline x) (S.filter (fun r -> not (is_reg r)) (fvs e));
  assert (S.is_empty (S.filter (fun r -> not (is_reg r)) (fvs e))); (* 未定義自由変数（本来は存在してはならない） *)
  let map, _ = g dest live (fvs (Ans(Nop))) e in
  try
    let vrmap = j map in
    showmap "" map vrmap;
    let vrmap = M.mapi (fun _ r -> (r, "")) vrmap in
    replace_reg vrmap e
  with RegAlloc_starvation r ->
    let _, _, graph = map in
    let vars = S.add r (M.find r graph) in
    let _, tfv = makefv dest (fvs (Ans(Nop))) (fvs (Ans(Nop))) e in
    let e, vars', _, _ = i dest M.empty M.empty vars (tfv, e) in
    let e, vars' = move_restore vars' M.empty e in
    if vars' = vars then raise (RegAlloc_starvation r);
    k' dest live e

let k dest live e =
  (* レジスタ依存関係による衝突回避のため *)
  let e = apply_exp (fun exp ->
    match exp with
    | Continue(x, yts, zs, ws, us) ->
       let tzs1 = List.map (fun z -> Id.genid z) zs in
       let tzs2 = List.map (fun z -> Id.genid z) zs in
       List.fold_left2 (fun e tz2 z -> Let([tz2, Type.Int], Mr(z), e)) (List.fold_left2 (fun e tz1 tz2 -> Let([tz1, Type.Int], Mr(tz2), e)) (Ans(Continue(x, yts, tzs1, ws, us))) tzs1 tzs2) tzs2 zs
    | _ -> Ans(exp)
  ) e in
  let _, tfv = makefv dest (fvs (Ans(Nop))) (fvs (Ans(Nop))) e in
  let e, _, _, _ = i dest M.empty M.empty S.empty (tfv, e) in
  (*let e = l S.empty e in*)
  k' dest live e
      
let h { name = Id.L(x); args = ys; body = e; ret = t } = (* 関数のレジスタ割り当て (caml2html: regalloc_h) *)
  prerr_endline x;
  let _, arg_regs, dest =
    List.fold_left
      (fun (i, arg_regs, dest) y ->
        let r = regs.(i) in
        (i + 1, r::arg_regs, y::dest)
      )
      (0, [], [])
      ys in  
  let e = Let(List.map (fun d -> (d, Type.Int)) dest, Tuple(arg_regs), e) in
  let a =
    match t with
    | Type.Unit -> Id.gentmp Type.Unit
    | _ -> regs.(0) in
  let e = specify_ret [(a, t)] e in
  let e = k [(a, t)] (S.of_list arg_regs) e in
  { name = Id.L(x); args = arg_regs; body = e; ret = t }

let f (Prog(data, vars, fundefs, e)) = (* プログラム全体のレジスタ割り当て (caml2html: regalloc_f) *)
  show fundefs e;
  Format.eprintf "register allocation: may take some time (up to a few minutes, depending on the size of functions)@.";
  let fundefs = List.map h fundefs in
  let e = specify_ret [(regs.(0), Type.Unit)] e in
  let e = k [(regs.(0), Type.Unit)] S.empty e in
  let p = Prog(data, vars, fundefs, e) in
  show fundefs e;
  p

