open KNormal

(* インライン展開する関数の最大サイズ (caml2html: inline_threshold) *)
let threshold = ref 50 (* Mainで-inlineオプションによりセットされる *)

let log = ref ""

let exenv = ref M.empty
let exfunc = ref M.empty
  
let rec size = function
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2)
  | Let(_, e1, e2) | LetRec({ body = e1 }, e2) -> 1 + size e1 + size e2
  | LetTuple(_, _, e) -> 1 + size e
  | _ -> 1

let memi x env =
  try (match M.find x env with Int(_) -> true | _ -> false)
  with Not_found -> false
let memf x env =
  try (match M.find x env with Float(_) -> true | _ -> false)
  with Not_found -> false
let memt x env =
  try (match M.find x env with Tuple(_) -> true | _ -> false)
  with Not_found -> false

let rec is_rec x = function
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | Let(_, e1, e2) -> (is_rec x e1) || (is_rec x e2)
  | LetRec({ name = _; args = _; body = e1 }, e2) -> (is_rec x e1) || (is_rec x e2)
  | App(x', _) -> if x' = x then true else false
  | LetTuple(_, _, e) -> is_rec x e
  | e -> false

let rec g env cenv = function (* インライン展開ルーチン本体 (caml2html: inline_g) *)
  | IfEq(x, y, e1, e2) ->
     let e1' = g env cenv e1 in
     let e2' = g env cenv e2 in
     IfEq(x, y, e1', e2')
  | IfLE(x, y, e1, e2) ->
     let e1' = g env cenv e1 in
     let e2' = g env cenv e2 in
     IfLE(x, y, e1', e2')
  | Let((x, t), e1, e2) ->
     let e1' = g env cenv e1 in
     let cenv =
       match e1' with
       | Int(_) | Float(_) -> M.add x e1' cenv
       | _ -> cenv
     in
     let e2' = g env cenv e2 in
     Let((x, t), e1', e2')
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) -> (* 関数定義の場合 (caml2html: inline_letrec) *)
     let env = M.add x (size e1, yts, e1, t) env in
     LetRec({ name = (x, t); args = yts; body = g env cenv e1}, g env cenv e2)
  | App(x, ys) as exp when M.mem x env -> (* 関数適用の場合 (caml2html: inline_app) *)
     let (size, zs, e, t) = M.find x env in
     let rec listconst _ =
       if M.mem x env then
	 List.fold_left2
	   (fun a (yt,t) y -> if M.mem y cenv then M.add yt ((M.find y cenv), t) a else a)
	   M.empty
	   zs
	   ys
       else
	 M.empty
     in
     if (size < !threshold) || (is_rec x e = false && size < !threshold * 50) then
       ((*log := !log ^ (Format.sprintf "inlining %s@." x);*)
	 Format.eprintf "inlining %s@." x;
	let env' =
	  List.fold_left2
  	    (fun env' (z, t) y -> M.add z y env')
	    M.empty
	    zs
	    ys in
	Alpha.g env' e)
     else
       let lc = listconst () in
       if lc <> M.empty then
	 (let fn = (M.fold (fun k (d,t) a -> (a ^ "_" ^ k ^ "_" ^ (
	   match d with
	   | Int(i) -> string_of_int i
	   | Float(f) -> string_of_float f
	   | _ -> assert false
	  ))) lc x)
	  in
	  let args = List.fold_left (fun a (y,t) -> if M.mem y lc then a else a@[(y,t)]) [] zs
	  in
	  let body = M.fold (fun k (y,t) a -> Let((k, t), y, a)) lc e
	  in
	  if M.mem fn env || M.mem fn !exenv then
	    ()
	  else
	    (exenv := M.add fn lc !exenv;
	     exfunc := M.add x { name = (fn, t); args = args; body = body } !exfunc);
	  App(fn, List.fold_left (fun a y -> if M.mem y cenv then a else a@[y]) [] ys))
       else
	 exp
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env cenv e)
  | e -> e

let rec i = function
  | IfEq(x, y, e1, e2) ->
     IfEq(x, y, i e1, i e2)
  | IfLE(x, y, e1, e2) ->
     IfLE(x, y, i e1, i e2)
  | Let((x, t), e1, e2) ->
     Let((x, t), i e1, i e2)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
     if M.mem x !exfunc then
       LetRec({ name = (x, t); args = yts; body = i e1}, LetRec(M.find x !exfunc, i e2))
     else
       LetRec({ name = (x, t); args = yts; body = i e1}, i e2)
  | LetTuple(xts, y, e) -> LetTuple(xts, y, i e)
  | e -> e

let f e =
  log := "";
  prerr_endline "start inlining...";
  exenv := M.empty;
  exfunc := M.empty;
  let e = g M.empty M.empty e in
  prerr_string !log;
  i e
