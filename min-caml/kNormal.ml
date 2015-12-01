(* give names to intermediate values (K-normalization) *)

type t = (* K正規化後の式 (caml2html: knormal_t) *)
  | Unit
  | Int of int
  | Float of float
  | Array of int
  | Neg of Id.t
  | Add of Id.t * Id.t
  | Sub of Id.t * Id.t
  | Xor of Id.t * Id.t
  | Or of Id.t * Id.t
  | And of Id.t * Id.t
  | Sll of Id.t * Id.t
  | Srl of Id.t * Id.t
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | FAbA of Id.t * Id.t
  | FAM of Id.t * Id.t * Id.t
  | FAbs of Id.t
  | Sqrt of Id.t
  | Cmp of int * Id.t * Id.t
  | If of Id.t * t * t (* 比較 + 分岐 (caml2html: knormal_branch) *)
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of Id.t * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | GetTuple of Id.t * int
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.t
  | ToFloat of Id.t
  | ToInt of Id.t
  | ToArray of Id.t
  | In of Id.t
  | Out of Id.t
  | Count
  | ShowExec
  | SetCurExec
  | GetExecDiff
  | GetHp of Id.t
  | SetHp of Id.t
  | ExtFunApp of Id.t * Id.t list
 and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

let negcond c = c lxor 7
  
let rec size = function
  | If(_, e1, e2)
  | Let(_, e1, e2) | LetRec({ body = e1 }, e2) -> 1 + size e1 + size e2
  | LetTuple(_, _, e) -> 1 + size e
  | _ -> 1

let rec fv_let x e1 e2 =
  S.union e1 (S.remove x e2)

let rec fv_if x e1 e2 =
  S.add x (S.union e1 e2)

let rec fv_func x yts e1 =
  let zs = S.diff e1 (S.of_list (List.map fst yts)) in
  S.diff zs (S.singleton x)
    
let rec fv_letrec x yts e1 e2 =
  let zs = fv_func x yts e1 in
  (S.union zs (S.diff e2 (S.singleton x)))

let rec fv_lettuple xs y e =
  S.add y (S.diff e (S.of_list (List.map fst xs)))

let rec fv = function (* 式に出現する（自由な）変数 (caml2html: knormal_fv) *)
  | Unit | Count | ShowExec | SetCurExec | GetExecDiff | Int(_) | Float(_) | Array(_) | ExtArray(_) -> S.empty
  | Neg(x) | FNeg(x) | Sqrt(x) | ToFloat(x) | ToInt(x) | ToArray(x) | In(x) | Out(x) | GetHp(x) | SetHp(x) | FAbs(x) | GetTuple(x, _) -> S.singleton x
  | Add(x, y) | Sub(x, y) | Xor(x, y) | Or(x, y) | And(x, y) | Sll(x, y) | Srl(x, y) | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | FAbA(x, y) | Get(x, y) | Cmp(_, x, y) -> S.of_list [x; y]
  | FAM(x, y, z) -> S.of_list [x; y; z]
  | If(x, e1, e2) ->
     fv_if x (fv e1) (fv e2)
  | Let((x, _), e1, e2) -> fv_let x (fv e1) (fv e2)
  | Var(x) -> S.singleton x
  | LetRec({ name = (x, _); args = yts; body = e1 }, e2) ->
     fv_letrec x yts (fv e1) (fv e2)
  | App(x, ys) -> S.of_list (x :: ys)
  | Tuple(xs) | ExtFunApp(_, xs) -> S.of_list xs
  | Put(x, y, z) -> S.of_list [x; y; z]
  | LetTuple(xs, y, e) -> fv_lettuple xs y (fv e)
     
let insert_let (e, t) k = (* letを挿入する補助関数 (caml2html: knormal_insert) *)
  match e with
  | Var(x) -> k x
  | _ ->
     let x = Id.gentmp t in
     let e', t' = k x in
     Let((x, t), e, e'), t'

let rec g env = function (* K正規化ルーチン本体 (caml2html: knormal_g) *)
  | Syntax.Unit -> Unit, Type.Unit
  | Syntax.Bool(b) -> Int(if b then 1 else 0), Type.Int (* 論理値true, falseを整数1, 0に変換 (caml2html: knormal_bool) *)
  | Syntax.Int(i) -> Int(i), Type.Int
  | Syntax.Float(d) -> Float(d), Type.Float
  | Syntax.Not(e) -> g env (Syntax.If(e, Syntax.Bool(false), Syntax.Bool(true)))
  | Syntax.Neg(e) ->
     insert_let (g env e)
	              (fun x -> Neg(x), Type.Int)
  | Syntax.Add(e1, e2) -> (* 足し算のK正規化 (caml2html: knormal_add) *)
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y -> Add(x, y), Type.Int))
  | Syntax.Sub(e1, e2) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y -> Sub(x, y), Type.Int))

  | Syntax.Mul(e1, e2) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y -> App("mul", [x; y]), Type.Int))
  | Syntax.Div(e1, e2) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y -> App("div", [x; y]), Type.Int))
  | Syntax.Xor(e1, e2) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y -> Xor(x, y), Type.Int))
  | Syntax.And(e1, e2) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y -> And(x, y), Type.Int))
  | Syntax.Or(e1, e2) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y -> Or(x, y), Type.Int))
  | Syntax.Sll(e1, e2) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y -> Sll(x, y), Type.Int))
  | Syntax.Srl(e1, e2) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y -> Srl(x, y), Type.Int))
  | Syntax.FNeg(e) ->
     insert_let (g env e)
	              (fun x -> FNeg(x), Type.Float)
  | Syntax.FAdd(e1, e2) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y -> FAdd(x, y), Type.Float))
  | Syntax.FSub(e1, e2) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y -> FSub(x, y), Type.Float))
  | Syntax.FMul(e1, e2) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y -> FMul(x, y), Type.Float))
  | Syntax.FDiv(e1, e2) ->
     insert_let (g env e1)
       (fun x -> insert_let (g env e2)
	 (fun y -> FDiv(x, y), Type.Float))
  | Syntax.Sqrt(e1) ->
     insert_let (g env e1)
	              (fun x -> Sqrt(x), Type.Float)
  | Syntax.Eq _ | Syntax.LE _ as cmp ->
                   g env (Syntax.If(cmp, Syntax.Bool(true), Syntax.Bool(false)))
  | Syntax.If(Syntax.Not(e1), e2, e3) -> g env (Syntax.If(e1, e3, e2)) (* notによる分岐を変換 (caml2html: knormal_not) *)
  | Syntax.If(Syntax.Eq(e1, e2), e3, e4) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y ->
	                                    let e3', t3 = g env e3 in
	                                    let e4', t4 = g env e4 in
					    insert_let (Cmp(2, x, y), Type.Int)
					      (fun z -> If(z, e3', e4'), t3)))
  | Syntax.If(Syntax.LE(e1, e2), e3, e4) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y ->
	                                    let e3', t3 = g env e3 in
	                                    let e4', t4 = g env e4 in
					    insert_let (Cmp(3, x, y), Type.Int)
					      (fun z -> If(z, e3', e4'), t3)))
  | Syntax.If(e1, e2, e3) -> g env (Syntax.If(Syntax.Eq(e1, Syntax.Bool(false)), e3, e2)) (* 比較のない分岐を変換 (caml2html: knormal_if) *)
  | Syntax.Let((x, t), e1, e2) ->
     (match e1 with
     | Syntax.LetDef((x, t), e1) -> g env (Syntax.Let((x, t), e1, e2))
     | Syntax.LetRecDef({ Syntax.name = (x, t); Syntax.args = yts; Syntax.body = e1 }) -> g env (Syntax.LetRec({ Syntax.name = (x, t); Syntax.args = yts; Syntax.body = e1 }, e2))
     | _ ->
        let e1', t1 = g env e1 in
        let e2', t2 = g (M.add x t env) e2 in
        Let((x, t), e1', e2'), t2)
  | Syntax.LetDef((x, t), e1) ->
     assert false
  | Syntax.Var(x) when M.mem x env -> Var(x), M.find x env
  | Syntax.Var(x) -> (* 外部配列の参照 (caml2html: knormal_extarray) *)
     (match M.find x !Typing.extenv with
      | Type.Array(_) as t -> ExtArray x, t
      | _ -> failwith (Printf.sprintf "external variable %s does not have an array or tuple type" x))
  | Syntax.LetRec({ Syntax.name = (x, t); Syntax.args = yts; Syntax.body = e1 }, e2) ->
     let env' = M.add x t env in
     let e2', t2 = g env' e2 in
     let e1', t1 = g (M.add_list yts env') e1 in
     LetRec({ name = (x, t); args = yts; body = e1' }, e2'), t2
  | Syntax.LetRecDef({ Syntax.name = (x, t); Syntax.args = yts; Syntax.body = e1 }) ->
     assert false
  | Syntax.App(Syntax.Var(f), e2s) when not (M.mem f env) -> (* 外部関数の呼び出し (caml2html: knormal_extfunapp) *)
     (match M.find f !Typing.extenv with
      | Type.Fun(_, t) ->
	       let rec bind xs = function (* "xs" are identifiers for the arguments *)
	         | [] -> ExtFunApp(f, xs), t
	         | e2 :: e2s ->
		          insert_let (g env e2)
		                     (fun x -> bind (xs @ [x]) e2s) in
	       bind [] e2s (* left-to-right evaluation *)
      | _ -> assert false)
  | Syntax.App(e1, e2s) ->
     (match g env e1 with
      | _, Type.Fun(_, t) as g_e1 ->
	       insert_let g_e1
	                  (fun f ->
	                   let rec bind xs = function (* "xs" are identifiers for the arguments *)
		                   | [] -> App(f, xs), t
		                   | e2 :: e2s ->
		                      insert_let (g env e2)
		                                 (fun x -> bind (xs @ [x]) e2s) in
	                   bind [] e2s) (* left-to-right evaluation *)
      | _ -> assert false)
  | Syntax.Tuple(es) ->
     let rec bind xs ts = function (* "xs" and "ts" are identifiers and types for the elements *)
	     | [] -> Tuple(xs), Type.Tuple(ts)
	     | e :: es ->
	        let _, t as g_e = g env e in
	        insert_let g_e
	                   (fun x -> bind (xs @ [x]) (ts @ [t]) es) in
     bind [] [] es
  | Syntax.LetTuple(xts, e1, e2) ->
     insert_let (g env e1)
	              (fun y ->
	               let e2', t2 = g (M.add_list xts env) e2 in
	               LetTuple(xts, y, e2'), t2)
  | Syntax.Array(e1, e2) ->
     insert_let (g env e1)
	              (fun x ->
	               let _, t2 as g_e2 = g env e2 in
	               insert_let g_e2
	                          (fun y ->
	                           let l =
		                           match t2 with
		                           | Type.Float -> "create_float_array_base"
		                           | _ -> "create_array_base" in
	                           App(l, [x; y]), Type.Array(t2)))
  | Syntax.ToFloat(e1) ->
     insert_let (g env e1)
	              (fun x -> ToFloat(x), Type.Float)
  | Syntax.ToInt(e1) ->
     insert_let (g env e1)
	              (fun x -> ToInt(x), Type.Int)
  | Syntax.ToArray(e1) ->
     insert_let (g env e1)
	              (fun x -> ToArray(x), Type.Array(Type.Int))
  | Syntax.In(e1) ->
     insert_let (g env e1)
	              (fun x -> In(x), Type.Int)
  | Syntax.Out(e1) ->
     insert_let (g env e1)
	              (fun x -> Out(x), Type.Unit)
  | Syntax.Count ->
     Count, Type.Unit
  | Syntax.ShowExec ->
     ShowExec, Type.Unit
  | Syntax.SetCurExec ->
     SetCurExec, Type.Unit
  | Syntax.GetExecDiff ->
     GetExecDiff, Type.Unit
  | Syntax.GetHp(e1) ->
     insert_let (g env e1)
	              (fun x -> GetHp(x), Type.Int)
  | Syntax.SetHp(e1) ->
     insert_let (g env e1)
	              (fun x -> SetHp(x), Type.Unit)
  | Syntax.Get(e1, e2) ->
     (match g env e1 with
      |	_, Type.Array(t) as g_e1 ->
	       insert_let g_e1
	                  (fun x -> insert_let (g env e2)
		                                     (fun y -> Get(x, y), t))
      | _ -> assert false)
  | Syntax.Put(e1, e2, e3) ->
     insert_let (g env e1)
	              (fun x -> insert_let (g env e2)
	                                   (fun y -> insert_let (g env e3)
		                                                      (fun z -> Put(x, y, z), Type.Unit)))

let f e = fst (g M.empty e)
