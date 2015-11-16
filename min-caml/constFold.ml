open KNormal

let exenv = ref M.empty
let exfunc = ref []

let memi x env =
  try (match M.find x env with Int(_) -> true | _ -> false)
  with Not_found -> false
let memf x env =
  try (match M.find x env with Float(_) -> true | _ -> false)
  with Not_found -> false
let memt x env =
  try (match M.find x env with Tuple(_) -> true | _ -> false)
  with Not_found -> false

let findi x env = (match M.find x env with Int(i) -> i | _ -> raise Not_found)
let findf x env = (match M.find x env with Float(d) -> d | _ -> raise Not_found)
let findt x env = (match M.find x env with Tuple(ys) -> ys | _ -> raise Not_found)	
  
let isconst y = 
  match y with
  | Int(_) | Float(_) -> true
  | _ -> false

let rec expandconst y env =
  try
    (match M.find y env with
    | Int(_) | Float (_) as e -> e
    | Var(v) -> expandconst v env
    | _ -> Var(y))
  with Not_found -> Var(y)
    
let rec h env fn fargs = function
  | Var(x) when memi x env -> (Int(findi x env), true)
  | Var(x) when memf x env -> (Float(findf x env), true)
  | Var(x) when memt x env -> (Tuple(findt x env), true)
  | Neg(x) when memi x env -> (Int(-(findi x env)), true)
  | Add(x, y) when memi x env && memi y env -> (Int(findi x env + findi y env), true) (* 足し算のケース (caml2html: constfold_add) *)
  | Sub(x, y) when memi x env && memi y env -> (Int(findi x env - findi y env), true)
  | Xor(x, y) when memi x env && memi y env -> (Int(findi x env lxor findi y env), true)
  | Or(x, y) when memi x env && memi y env -> (Int(findi x env lor findi y env), true)
  | And(x, y) when memi x env && memi y env -> (Int(findi x env land findi y env), true)
  | Sll(x, y) when memi x env && memi y env -> (Int(findi x env lsl findi y env), true)
  | Srl(x, y) when memi x env && memi y env -> (Int(findi x env lsr findi y env), true)
  | FNeg(x) when memf x env -> (Float(-.(findf x env)), true)
  | FAdd(x, y) when memf x env && memf y env -> (Float(findf x env +. findf y env), true)
  | FSub(x, y) when memf x env && memf y env -> (Float(findf x env -. findf y env), true)
  | FMul(x, y) when memf x env && memf y env -> (Float(findf x env *. findf y env), true)
  | FDiv(x, y) when memf x env && memf y env -> (Float(findf x env /. findf y env), true)
  | Sqrt(x) when memf x env -> (Float(sqrt (findf x env)), true)
  | IfEq(x, y, e1, e2) when memi x env && memi y env ->
     let e1', f1 = h env fn fargs e1 in
     let e2', f2 = h env fn fargs e2 in
     let f = f1 || f2 in
     if findi x env = findi y env then (e1', f) else (e2', f)
  | IfEq(x, y, e1, e2) when memf x env && memf y env ->
     let e1', f1 = h env fn fargs e1 in
     let e2', f2 = h env fn fargs e2 in
     let f = f1 || f2 in
     if findf x env = findf y env then (e1', f) else (e2', f)
  | IfEq(x, y, e1, e2) ->
     let e1', f1 = h env fn fargs e1 in
     let e2', f2 = h env fn fargs e2 in
     let f = f1 && f2 in
     (IfEq(x, y, e1', e2'), f)
  | IfLE(x, y, e1, e2) when memi x env && memi y env ->
     let e1', f1 = h env fn fargs e1 in
     let e2', f2 = h env fn fargs e2 in
     let f = f1 || f2 in
     if findi x env <= findi y env then (e1', f) else (e2', f)
  | IfLE(x, y, e1, e2) when memf x env && memf y env ->
          let e1', f1 = h env fn fargs e1 in
     let e2', f2 = h env fn fargs e2 in
     let f = f1 || f2 in
     if findf x env <= findf y env then (e1', f) else (e2', f)
  | IfLE(x, y, e1, e2) ->
     let e1', f1 = h env fn fargs e1 in
     let e2', f2 = h env fn fargs e2 in
     let f = f1 && f2 in
     (IfLE(x, y, e1', e2'), f)
  | Let((x, t), e1, e2) -> (* letのケース (caml2html: constfold_let) *)
     let e1', f1 = h env fn fargs e1 in
     let env =
       (match e1' with
       | Int (_) | Float(_) | Tuple(_) -> (M.add x e1' env)
       | _ -> env)
     in
     let e2', f2 = h env fn fargs e2 in
     let f = f1 && f2 in
     (Let((x, t), e1', e2'), f)
  | LetRec({ name = (x, t); args = ys; body = e1 }, e2) ->
     let e1', f1 = h env fn fargs e1 in
     let e2', f2 = h env fn fargs e2 in
     let f = f1 && f2 in
     (LetRec({ name = (x, t); args = ys; body = e1' }, e2'), f)
  | LetTuple(xts, y, e) when memt y env ->
     h env fn fargs (List.fold_left2
		       (fun e' xt z -> Let(xt, Var(z), e'))
		       e
		       xts
		       (findt y env))
  | LetTuple(xts, y, e) ->
     let e', f = h env fn fargs e in
     (LetTuple(xts, y, e'), f)
  | App(x, yts) as e when x = fn ->
     (e, List.fold_left2
       (fun flag y y' ->
	 if isconst y then
	   match y, expandconst y' env with
	   | Int(i), Int(i') when i = i' -> flag
	   | Float(f), Float(f') when f = f' -> flag
	   | _ -> false
	 else
	   flag)
       true
       fargs
       yts)
  | e -> (e, true)

let rec i = function
  | IfEq(x, y, e1, e2) ->
     IfEq(x, y, i e1, i e2)
  | IfLE(x, y, e1, e2) ->
     IfLE(x, y, i e1, i e2)
  | Let((x, t), e1, e2) ->
     Let((x, t), i e1, i e2)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
     let e2 =
       List.fold_right
	 (fun (fn, func) e -> if x = fn then LetRec(func, e) else e)
	 !exfunc
	 (i e2)
     in
     LetRec({ name = (x, t); args = yts; body = i e1}, e2)
  | LetTuple(xts, y, e) -> LetTuple(xts, y, i e)
  | e -> e

let rec g env fenv gflag = function (* 定数畳み込みルーチン本体 (caml2html: constfold_g) *)
  | Var(x) when memi x env -> Int(findi x env)
  | Var(x) when memf x env -> Float(findf x env)
  | Var(x) when memt x env -> Tuple(findt x env)
  | Neg(x) when memi x env -> Int(-(findi x env))
  | Add(x, y) when memi x env && memi y env -> Int(findi x env + findi y env) (* 足し算のケース (caml2html: constfold_add) *)
  | Sub(x, y) when memi x env && memi y env -> Int(findi x env - findi y env)
  | Xor(x, y) when memi x env && memi y env -> Int(findi x env lxor findi y env)
  | Or(x, y) when memi x env && memi y env -> Int(findi x env lor findi y env)
  | And(x, y) when memi x env && memi y env -> Int(findi x env land findi y env)
  | Sll(x, y) when memi x env && memi y env -> Int(findi x env lsl findi y env)
  | Srl(x, y) when memi x env && memi y env -> Int(findi x env lsr findi y env)
  | FNeg(x) when memf x env -> Float(-.(findf x env))
  | FAdd(x, y) when memf x env && memf y env -> Float(findf x env +. findf y env)
  | FSub(x, y) when memf x env && memf y env -> Float(findf x env -. findf y env)
  | FMul(x, y) when memf x env && memf y env -> Float(findf x env *. findf y env)
  | FDiv(x, y) when memf x env && memf y env -> Float(findf x env /. findf y env)
  | Sqrt(x) when memf x env -> Float(sqrt (findf x env))
  | IfEq(x, y, e1, e2) when memi x env && memi y env -> if findi x env = findi y env then g env fenv gflag e1 else g env fenv gflag e2
  | IfEq(x, y, e1, e2) when memf x env && memf y env -> if findf x env = findf y env then g env fenv gflag e1 else g env fenv gflag e2
  | IfEq(x, y, e1, e2) -> IfEq(x, y, g env fenv gflag e1, g env fenv gflag e2)
  | IfLE(x, y, e1, e2) when memi x env && memi y env -> if findi x env <= findi y env then g env fenv gflag e1 else g env fenv gflag e2
  | IfLE(x, y, e1, e2) when memf x env && memf y env -> if findf x env <= findf y env then g env fenv gflag e1 else g env fenv gflag e2
  | IfLE(x, y, e1, e2) -> IfLE(x, y, g env fenv gflag e1, g env fenv gflag e2)
  | Let((x, t), e1, e2) -> (* letのケース (caml2html: constfold_let) *)
     let e1' = g env fenv gflag e1 in
     let env =
       (match e1' with
       | Int (_) | Float(_) | Tuple(_) -> (M.add x e1' env)
       | _ -> env)
     in
     let e2' = g env fenv gflag e2 in
     Let((x, t), e1', e2')
  | LetRec({ name = (x, t); args = ys; body = e1 }, e2) ->
     let fenv = M.add x (ys, e1, t) fenv in
     LetRec({ name = (x, t); args = ys; body = g env fenv gflag e1 }, g env fenv gflag e2)
  | LetTuple(xts, y, e) when memt y env ->
     g env fenv gflag (List.fold_left2
		   (fun e' xt z -> Let(xt, Var(z), e'))
		   e
		   xts
		   (findt y env))
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env fenv gflag e)
  | App(x, ys) as exp when gflag && M.mem x fenv ->
     let (zs, e, t) = M.find x fenv in
     let cys = List.fold_left (fun a y -> a@[expandconst y env]) [] ys in
     let listconst _ =
       List.fold_left2
	 (fun a (yn,t) y -> if isconst y then
	     M.add yn (y, t) a
	   else
	     a)
	 M.empty
	 zs
	 cys
     in
     let lc = listconst () in
     if lc <> M.empty then
       (let fn = String.map (fun c -> if c = '-' then 'M' else c) (M.fold (fun k (d,t) a -> a ^ "_" ^ k ^ "_" ^ (
	    match d with
	    | Int(i) -> string_of_int i
	    | Float(f) -> string_of_float f
	    | _ -> assert false
	   )) lc x)
	in
	let body, flag = h M.empty x cys (M.fold (fun k (y,t) a -> Let((k, t), y, a)) lc e) in
	let rec opt n e =
	  if n = 0 then e else
	    let exenv2 = !exenv in
	    let exfunc2 = !exfunc in
	    let e' = g M.empty M.empty false e in
	    exenv := exenv2;
	    exfunc := exfunc2;
	    if e = e' then
	      e
	    else opt (n - 1) e'
	in
	let body = opt 1000 body in
	let is_explosive _ =
	    let exenv2 = !exenv in
	    let exfunc2 = !exfunc in
	    let rec cnt = function
	      | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) -> (cnt e1) + (cnt e2)
	      | Let(_, e1, e2) -> (cnt e1) + (cnt e2)
	      | LetRec(_, e) -> cnt e
	      | LetTuple(_, _, e) -> cnt e
	      | App(x', _) when x = x' -> 1
	      | _ -> 0
	    in
	    let flag = cnt body > 1 in
	    exenv := exenv2;
	    exfunc := exfunc2;
	    flag
	in
	if not flag || is_explosive () || (KNormal.size body) - (M.cardinal lc) >= (KNormal.size e) - 3 then
	  exp
	else
	  (let fn = String.map (fun c -> if c = '-' then 'M' else c) (M.fold (fun k (d,t) a -> a ^ "_" ^ k ^ "_" ^ (
	    match d with
	    | Int(i) -> string_of_int i
	    | Float(f) -> string_of_float f
	    | _ -> assert false
	   )) lc x)
	   in
	   (if M.mem fn fenv || M.mem fn !exenv then
	    ()
	    else
	       (Format.eprintf "generating function %s@." fn;
		let args = List.fold_left (fun a (y,t) -> if M.mem y lc then a else a@[(y,t)]) [] zs
		in
		let t = match t with
		  | Type.Fun(ts, rt) ->
		     let ts = List.fold_left2
		       (fun a (y,_) t ->
			 if M.mem y lc then a else a@[t])
		       []
		       zs
		       ts
		     in
		     Type.Fun(ts, rt)
		  | _ -> assert false
		in
		exenv := M.add fn lc !exenv;
		exfunc := (x, { name = (fn, t); args = args; body = Alpha.f body }) :: !exfunc));
	   App(fn, (List.fold_left
		      (fun a y -> if isconst y then a else
			  match y with
			  | Var(y) -> a@[y]
			  | _ -> assert false
		      ) [] cys))))
     else
       exp
  | e -> e
     
let rec f e =
  exenv := M.empty;
  exfunc := [];
  i (g M.empty M.empty true e)
