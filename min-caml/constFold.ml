open KNormal

let exenv = ref M.empty
let ofenv = ref S.empty

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
  | Int(_) | Float(_) | Array(_) -> true
  | _ -> false

let rec expandconst y env =
  try
    (match M.find y env with
    | Int(_) | Float (_) | Array(_) as e -> e
    | Var(v) -> expandconst v env
    | _ -> Var(y))
  with Not_found -> Var(y)

(* プログラム解析 *)
(* gethp, sethpについては必要ないので省略 *)
(* 戻り値：停止性(bool)、爆発性（int）*)
let rec h env fn = function
  | Var(x) when memi x env -> (Int(findi x env), true, 0)
  | Var(x) when memf x env -> (Float(findf x env), true, 0)
  | Var(x) when memt x env -> (Tuple(findt x env), true, 0)
  | ToArray(x) when memi x env -> (Array(findi x env), true, 0)
  | Neg(x) when memi x env -> (Int(-(findi x env)), true, 0)
  | Add(x, y) when memi x env && memi y env -> (Int(findi x env + findi y env), true, 0) (* 足し算のケース (caml2html: constfold_add) *)
  | Sub(x, y) when memi x env && memi y env -> (Int(findi x env - findi y env), true, 0)
  | Xor(x, y) when memi x env && memi y env -> (Int(findi x env lxor findi y env), true, 0)
  | Or(x, y) when memi x env && memi y env -> (Int(findi x env lor findi y env), true, 0)
  | And(x, y) when memi x env && memi y env -> (Int(findi x env land findi y env), true, 0)
  | Sll(x, y) when memi x env && memi y env -> (Int(findi x env lsl findi y env), true, 0)
  | Srl(x, y) when memi x env && memi y env -> (Int(findi x env lsr findi y env), true, 0)
  | FNeg(x) when memf x env -> (Float(-.(findf x env)), true, 0)
  | FAdd(x, y) when memf x env && memf y env -> (Float(findf x env +. findf y env), true, 0)
  | FSub(x, y) when memf x env && memf y env -> (Float(findf x env -. findf y env), true, 0)
  | FMul(x, y) when memf x env && memf y env -> (Float(findf x env *. findf y env), true, 0)
  | FDiv(x, y) when memf x env && memf y env -> (Float(findf x env /. findf y env), true, 0)
  | FAbA(x, y) when memf x env && memf y env -> (Float(abs_float(findf x env +. findf y env)), true, 0)
  | FAM(x, y, z) when memf x env && memf y env && memf z env -> (Float(findf x env *. findf y env +. findf z env), true, 0)
  | FAbs(x) when memf x env -> (Float(abs_float(findf x env)), true, 0)
  | Sqrt(x) when memf x env -> (Float(sqrt (findf x env)), true, 0)
  | Cmp(c, x, y) when memi x env && memi y env ->
     let x = findi x env in
     let y = findi y env in
     let i = 
     if c land 1 <> 0 && x < y then 1 else
       if c land 2 <> 0 && x = y then 1 else
	 if c land 4 <> 0 && x > y then 1 else
	   0
     in
     (Int(i), true, 0)
  | Cmp(c, x, y) when memf x env && memf y env ->
     let x = findf x env in
     let y = findf y env in
     let i = 
     if c land 1 <> 0 && x < y then 1 else
       if c land 2 <> 0 && x = y then 1 else
	 if c land 4 <> 0 && x > y then 1 else
	   0
     in
     (Int(i), true, 0)
  | If(x, e1, e2) when memi x env ->
     let e1', f1, r1 = h env fn e1 in
     let e2', f2, r2 = h env fn e2 in
     let f = f1 || f2 in
     let x = findi x env in
     if x <> 0 then (e1', f, r1) else (e2', f, r2)
  | If(x, e1, e2) ->
     let e1', f1, r1 = h env fn e1 in
     let e2', f2, r2 = h env fn e2 in
     let f = f1 && f2 in
     (If(x, e1', e2'), f, r1 + r2)
  | Let((x, t), e1, e2) -> (* letのケース (caml2html: constfold_let) *)
     let e1', f1, r1 = h env fn e1 in
     let env =
       (match e1' with
       | Int (_) | Float(_) | Tuple(_) | Array (_) -> (M.add x e1' env)
       | _ -> env)
     in
     let e2', f2, r2 = h env fn e2 in
     let f = f1 && f2 in
     (Let((x, t), e1', e2'), f, r1 + r2)
  | LetRec({ name = (x, t); args = ys; body = e1 }, e2) ->
     assert false;
     let e1', f1, r1 = h env fn e1 in
     let e2', f2, r2 = h env fn e2 in
     let f = f1 && f2 in
     (LetRec({ name = (x, t); args = ys; body = e1' }, e2'), f, r2)
  | LetTuple(xts, y, e) when memt y env ->
     h env fn (List.fold_left2
		 (fun e' xt z -> Let(xt, Var(z), e'))
		 e
		 xts
		 (findt y env))
  | LetTuple(xts, y, e) ->
     let e', f, r = h env fn e in
     (LetTuple(xts, y, e'), f, r)
  | App(x, yts) as e when x = fn ->
     (e, false, 1)
  | ToInt(x) when memf x env -> (Int(Type.conv_float(findf x env)), true, 0)
  | ToFloat(x) when memi x env -> (Float(Type.conv_int(findi x env)), true, 0)
  | e -> (e, true, 0)

let gencys ys env = List.fold_left (fun a y -> a@[expandconst y env]) [] ys

let listconst cys zs =
  List.fold_left2
    (fun a (yn,t) y -> if isconst y then
	M.add yn (y, t) a
      else
	a)
    M.empty
    zs
    cys
     
let genfn x lc =
  String.map (fun c -> if c = '-' then 'M' else c) (M.fold (fun k (d,t) a -> a ^ "_" ^ k ^ "_" ^ (
    match d with
    | Int(i) -> string_of_int i
    | Float(f) -> string_of_float f
    | Array(i) -> string_of_int i
    | _ -> assert false
  )) lc x)
     
let rec generate x fn t lc zs body =
  (*Format.eprintf "generating function %s@." fn;*)
  if M.mem fn !exenv then
    false
  else
    (
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
      exenv := M.add fn (x, { name = (fn, t); args = args; body = Alpha.f body }) !exenv;
      true
    )

let genarg cys =
  List.fold_left
    (fun a y -> if isconst y then a else
	match y with
	| Var(y) -> a@[y]
	| _ -> assert false
    ) [] cys
    
(* getとかを追加 *)
let rec g env fenv fn = function (* 定数畳み込みルーチン本体 (caml2html: constfold_g) *)
  | Var(x) when memi x env -> Int(findi x env), false
  | Var(x) when memf x env -> Float(findf x env), false
  | Var(x) when memt x env -> Tuple(findt x env), false
  | ToArray(x) when memi x env -> Array(findi x env), false
  | Neg(x) when memi x env -> Int(-(findi x env)), false
  | Add(x, y) when memi x env && memi y env -> Int(findi x env + findi y env), false
  | Sub(x, y) when memi x env && memi y env -> Int(findi x env - findi y env), false
  | Xor(x, y) when memi x env && memi y env -> Int(findi x env lxor findi y env), false
  | Or(x, y) when memi x env && memi y env -> Int(findi x env lor findi y env), false
  | And(x, y) when memi x env && memi y env -> Int(findi x env land findi y env), false
  | And(x, y) when memi x env && (findi x env = 2147483647) -> FAbs(y), false
  | And(x, y) when memi y env && (findi y env = 2147483647) -> FAbs(x), false
  | Sll(x, y) when memi x env && memi y env -> Int(findi x env lsl findi y env), false
  | Srl(x, y) when memi x env && memi y env -> Int(findi x env lsr findi y env), false
  | FNeg(x) when memf x env -> Float(-.(findf x env)), false
  | FAdd(x, y) when memf x env && memf y env -> Float(findf x env +. findf y env), false
  | FSub(x, y) when memf x env && memf y env -> Float(findf x env -. findf y env), false
  | FMul(x, y) when memf x env && memf y env -> Float(findf x env *. findf y env), false
  | FDiv(x, y) when memf x env && memf y env -> Float(findf x env /. findf y env), false
  | FAbA(x, y) when memf x env && memf y env -> Float(abs_float(findf x env +. findf y env)), false
  | FAM(x, y, z) when memf x env && memf y env && memf z env -> Float(findf x env *. findf y env +. findf z env), false
  | FAbs(x) when memf x env -> Float(abs_float(findf x env)), false
  | Sqrt(x) when memf x env -> Float(sqrt (findf x env)), false
  | Cmp(c, x, y) when memi x env && memi y env ->
     let x = findi x env in
     let y = findi y env in
     let i = 
     if c land 1 <> 0 && x < y then 1 else
       if c land 2 <> 0 && x = y then 1 else
	 if c land 4 <> 0 && x > y then 1 else
	   0
     in
     Int(i), false
  | Cmp(c, x, y) when memf x env && memf y env ->
     let x = findf x env in
     let y = findf y env in
     let i = 
     if c land 1 <> 0 && x < y then 1 else
       if c land 2 <> 0 && x = y then 1 else
	 if c land 4 <> 0 && x > y then 1 else
	   0
     in
     Int(i), false
  | If(x, e1, e2) when memi x env ->
     let x = findi x env in
     if x <> 0 then g env fenv fn e1 else g env fenv fn e2
  | If(x, e1, e2) ->
     let e1, f1 = g env fenv fn e1 in
     let e2, f2 = g env fenv fn e2 in
     If(x, e1, e2), f1 || f2
  | Let((x, t), e1, e2) -> (* letのケース (caml2html: constfold_let) *)
     let e1, f1 = g env fenv fn e1 in
     let env =
       (match e1 with
       | Int (_) | Float(_) | Tuple(_) | Array(_) -> (M.add x e1 env)
       | _ -> env)
     in
     let e2, f2 = g env fenv fn e2 in
     Let((x, t), e1, e2), f1 || f2
  | LetRec({ name = (x, t); args = ys; body = e1 }, e2) ->
     let fenv = M.add x (ys, e1, t) fenv in
     let e1, f1 = g env fenv fn e1 in
     let e2, f2 = g env fenv fn e2 in
     let e2 =
       M.fold
	 (fun _ (fn, func) e -> if x = fn then LetRec(func, e) else e)
	 !exenv
	 e2
     in
     LetRec({ name = (x, t); args = ys; body = e1 }, e2), f1 || f2
  | LetTuple(xts, y, e) when memt y env ->
     g env fenv fn (List.fold_left2
				   (fun e' xt z -> Let(xt, Var(z), e'))
				   e
				   xts
				   (findt y env))
  | LetTuple(xts, y, e) ->
     let e, f = g env fenv fn e in
     LetTuple(xts, y, e), f
  | App(x, ys) as exp when M.mem x fenv && fn <> x ->
     let (zs, e, t) = M.find x fenv in
     let cys = gencys ys env in
     let lc = listconst cys zs in
     let ffold body = 
       let fn = genfn x lc in
       let f = if M.mem fn fenv then
	   false
	 else
	   generate x fn t lc zs body in
       App(fn, genarg cys), f
     in
     let opt fn limit e =
       let rec opt_sub e =
	 let e', f = g env fenv x (Assoc.f (Beta.f e)) in
	 if e = e' || KNormal.size e > limit then
	   (
	     (if e <> e' then ofenv := S.add fn !ofenv;);
	     e, f
	   )
	 else
	   let e', f' = opt_sub e' in
	   e', f || f'
       in
       let e', f = opt_sub e in
       let e = Elim.f e' in
       e, f
     in
     if lc <> M.empty then
       (
	 let fn = genfn x lc in
	 let body = (M.fold (fun k (y,t) a -> Let((k, t), y, a)) lc e) in
	 if M.mem fn fenv || M.mem fn !exenv then
	   ffold body
	 else
	   if not (Inline.is_rec x body) then
	     if S.mem fn !ofenv then
	       exp, false
	     else
	       let body', f = opt fn ((KNormal.size e) * 2) body in
	       if KNormal.size body' < (KNormal.size e) / 2 || f then
		 ffold body'
	       else
		 exp, false
	   else
	     let body, sflag, r = h M.empty x (M.fold (fun k (y,t) a -> Let((k, t), y, a)) lc body) in
	     if not sflag || r > 1 then
	       exp, false
	     else
	       if S.mem fn !ofenv then
		 exp, false
	       else
		 let body', f = opt fn ((KNormal.size e) * 4) body in
		 if KNormal.size body' < 2 * KNormal.size e || f then
		   ffold body'
		 else
		   exp, false
       )
     else
       exp, false
  | App(x, ys) as exp when fn = x ->
     let (zs, e, _) = M.find x fenv in
     let cys = gencys ys env in
     let lc = listconst cys zs in
     (if lc <> M.empty then
	 let env' =
	   List.fold_left2
  	     (fun env' (z, t) y -> M.add z y env')
	     M.empty
	     zs
	     ys in
	 Alpha.g env' e
      else
	 exp), false
  | ToInt(x) when memf x env -> Int(Type.conv_float(findf x env)), false
  | ToFloat(x) when memi x env -> Float(Type.conv_int(findi x env)), false
  | e -> e, false

let rec f e =
  ofenv := S.empty;
  exenv := M.empty;
  let e, _ = g M.empty M.empty "" e in
  e
