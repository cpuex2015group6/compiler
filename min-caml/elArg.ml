open KNormal

let argenv = ref M.empty

let rec h fn nfn cargs ws = function
  | If(c, x, y, e1, e2) ->
     If(c, x, y, h fn nfn cargs ws e1, h fn nfn cargs ws e2)
  | While(x, ys, zs, e) ->
     While(x, ys, zs, h fn nfn cargs ws e)
  | Let(xt, e1, e2) ->
     Let(xt, h fn nfn cargs ws e1, h fn nfn cargs ws e2)
  | LetRec({ name = xt; args = ys; body = e1 }, e2) ->
     LetRec({ name = xt; args = ys; body = h fn nfn cargs ws e1 }, h fn nfn cargs ws e2)
  | LetTuple(xts, y, e) ->
     LetTuple(xts, y, h fn nfn cargs ws e)
  | App(x, ys) when fn = x ->
     let ys = List.fold_left2 (fun nys y (z, t) -> if M.mem z cargs then nys else nys@[y]) [] ys ws in
     App(nfn, ys)
  | e -> e

let rm_arg = List.fold_left2 (fun nys y ry -> match ry with | Some _ -> nys | None -> nys@[y]) []
let rm_arg_t = List.fold_left2 (fun nyts yt ry -> match ry with | Some _ -> nyts | None -> nyts@[yt]) []
     
(* While argのelimination判定 *)
let rec i x ys = function
  | If(_, _, _, e1, e2) ->
     List.map2 (fun y1 y2 ->
       match y1, y2 with
       | Some(yt), Some(_) -> Some(yt)
       | _ -> None
     ) (i x ys e1) (i x ys e2)
  | While(_, _, _, e) -> i x ys e
  | Let(_, _, e) ->
     (* exp内にはcontinueはないはず *)
     i x ys e
  | LetRec(_) -> assert false
  | LetTuple(_, _, e) -> i x ys e
  | Continue(x', _, zs) when x = x' -> List.map2 (fun y z ->
    match y, z with
    | Some(y), z when y = z -> Some(y)
    | _ -> None
  ) ys zs
  | e -> ys

(* While arg 除去 *)
let rec j x rys = function
  | If(c, x', y', e1, e2) ->
     If(c, x', y', j x rys e1, j x rys e2)
  | While(x', yts, zs, e) ->
     While(x', yts, zs, j x rys e)
  | Let(xt, e1, e2) ->
     Let(xt, e1, j x rys e2)
  | LetRec(_) -> assert false
  | LetTuple(xts, y, e) ->
     LetTuple(xts, y, j x rys e)
  | Continue(x', yts, zs) when x = x' ->
     Continue(x, rm_arg_t yts rys, rm_arg zs rys)
  | e -> e
  
let rec g env fenv fn = function
  | If(c, x, y, e1, e2) ->
     If(c, x, y, g env fenv fn e1, g env fenv fn e2)
  | While(x, yts, zs, e) ->
     let rys = i x (List.map (fun (y, _) -> Some(y)) yts) e in
     let e = j x rys e in
     let env' = List.fold_left2 (fun env' ry z ->
       match ry with
       | Some(ry) -> M.add ry z env'
       | None -> env') M.empty rys zs in
     let e = if env' = M.empty then e else Alpha.g env' e in
     While(x, rm_arg_t yts rys, rm_arg zs rys, g env fenv fn e)
  | Let((x, t), e1, e2) ->
     let e1 = g env fenv fn e1 in
     let e2 = g (M.add x (e1, t) env) fenv fn e2 in
     Let((x, t), e1, e2)
  | LetRec({ name = (x, t); args = ys; body = e1 }, e2) ->
     if fn <> "" then assert false;
     let fenv = M.add x (ys, e1, t) fenv in
     let e2 = g env fenv fn e2 in
     let e1 = g env fenv x e1 in
     if M.mem x !argenv then
       (
	       let cargs = M.find x !argenv in
	       if M.cardinal cargs <> 0 then
	         (
	           let e1 = M.fold (fun k (y, t) a -> Let((k, t), y, a)) cargs e1 in
	           let fn = Id.genid (M.fold (fun k (y, t) x -> x ^ "_cv_" ^ k) cargs x) in
	           let e1 = h x fn cargs ys e1 in
	           let e2 = h x fn cargs ys e2 in
	           let ys' = List.fold_left(fun nys (y, t) -> if M.mem y cargs then nys else nys@[(y, t)]) [] ys in
	           (*Format.eprintf "remove const argument(s) %s from %s and generate %s@."
	             (Id.pp_list (M.fold (fun k _ l -> k::l) cargs [])) x fn;*)
	           match t with
	           | Type.Fun(ats, rt) ->
		            let ats = List.fold_left2 (fun nats at (y, t) -> if M.mem y cargs then nats else nats@[at]) [] ats ys in
		            g env fenv "" (LetRec({ name = (fn, Type.Fun(ats, rt)); args = ys'; body = e1 }, e2))
	           | _ -> assert false
	         )
	       else
	         LetRec({ name = (x, t); args = ys; body = e1 }, e2)
       )
     else
       LetRec({ name = (x, t); args = ys; body = e1 }, e2)
  | LetTuple(xts, y, e) ->
     LetTuple(xts, y, g env fenv fn e)
  | App(x, ys) as exp when fn = x ->
     if M.mem x !argenv then
       let (zs, e, t) = M.find x fenv in
       let cys = ConstFold.gencys ys env in
       let lc = ConstFold.listconst cys zs in
       let pargs = M.find x !argenv in
       let narg = M.fold
	       (fun k (d, t) nm ->
	         try (let e, _ = M.find k lc in
		            match e, d with
		            | Int(x), Int(y) when x = y ->
		               M.add k (d, t) nm
		            | Float(x), Float(y) when x = y ->
		               M.add k (d, t) nm
		            | Array(x), Array(y) when x = y ->
		               M.add k (d, t) nm
		            | _ ->
		               nm)
	         with Not_found ->
	           if List.fold_left2
	             (fun f y (z, _) -> if k = z then k = y else f)
	             true ys zs then
	             M.add k (d, t) nm
	           else
	             nm)
	       pargs
	       M.empty
       in
       argenv := M.mapi (fun k d -> if k = x then narg else d) !argenv
     else
       ();
    exp
  | App(x, ys) as exp when M.mem x !argenv ->
     let (zs, e, t) = M.find x fenv in
     let cys = ConstFold.gencys ys env in
     let lc = ConstFold.listconst cys zs in
     let pargs = M.find x !argenv in
     let narg = M.fold
       (fun k (d, t) nm ->
	       try (let e, t = M.find k lc in
	            match e, d with
	            | Int(x), Int(y) when x = y ->
		             M.add k (d, t) nm
	            | Float(x), Float(y) when x = y ->
		             M.add k (d, t) nm
	            | Array(x), Array(y) when x = y ->
		             M.add k (d, t) nm
	            | _ ->
		             nm)
	       with Not_found -> nm)
       pargs
       M.empty
     in
     argenv := M.mapi (fun k d -> if k = x then narg else d) !argenv;
     exp
  | App(x, ys) as exp ->
     let (zs, e, t) = M.find x fenv in
     let cys = ConstFold.gencys ys env in
     let lc = ConstFold.listconst cys zs in
     argenv := (M.add x lc !argenv);
     exp
  | e -> e


let rec f e =
  argenv := M.empty;
  g M.empty M.empty "" e

