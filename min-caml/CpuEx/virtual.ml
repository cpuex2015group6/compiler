(* translation into PowerPC assembly (infinite number of virtual registers) *)

open Asm

let data = ref [] (* 浮動小数点数の定数テーブル *)
let vars = ref [] (* グローバル変数を格納するテーブル *)

let classify xts ini addi =
  List.fold_left
    (fun acc (x, t) -> match t with
       | Type.Unit -> acc
       | _ -> addi acc x t) ini xts

let expand xts ini addi = 
  classify
    xts
    ini
    (fun (offset, acc) x t -> (offset + 1, addi x t offset acc))

let rec g env = function (* 式の仮想マシンコード生成 *)
  | Closure.Unit -> Ans (Nop)
  | Closure.Int (i) ->
     if i >= 0 && i < 32768 then
       Ans (Li (C(i)))
     else
       let conv_unsinged i =
	 if i >= 0 then i else
	   0x100000000 + i
       in
       let i = conv_unsinged i in
       let l = 
	 try
	   let (l, _) = List.find (fun (_, d') -> i = d') !data in
	   l
	 with Not_found ->
	   let l = Id.L (Id.genid "l") in
	   data := (l, i) :: !data;
	   l in
       Ans (Li (L(l)))
  | Closure.Float (d) -> 
     let d = Type.conv_float d in
     if d >= 0 && d < 32768 then
       Ans (FLi (C(d)))
     else
       let l = 
	 try
	   let (l, _) = List.find (fun (_, d') -> d = d') !data in
	   l
	 with Not_found ->
	   let l = Id.L (Id.genid "l") in
	   data := (l, d) :: !data;
	   l in
       Ans (FLi (L(l)))
  | Closure.Neg (x) ->
     let y = Id.genid "t" in
     Let((y, Type.Int), Li (C(0)), Ans(Sub(y, V(x))))
  | Closure.Add (x, y) -> Ans (Add (x, V (y)))
  | Closure.Sub (x, y) -> Ans (Sub (x, V (y)))
  | Closure.Xor (x, y) -> Ans (Xor (x, V (y)))
  | Closure.Or (x, y) -> Ans (Or (x, V (y)))
  | Closure.And (x, y) -> Ans (And (x, V (y)))
  | Closure.Sll (x, y) -> Ans (Sll (x, V (y)))
  | Closure.Srl (x, y) -> Ans (Srl (x, V (y)))
  | Closure.FNeg (x) ->
     let y = Id.genid "t" in
     Let((y, Type.Float), Li (C(0)), Ans(FSub(y, x)))
  | Closure.FAdd (x, y) -> Ans (FAdd (x, y))
  | Closure.FSub (x, y) -> Ans (FSub (x, y))
  | Closure.FMul (x, y) -> Ans (FMul (x, y))
  | Closure.FDiv (x, y) -> Ans (FDiv (x, y))
  | Closure.FAM (x, y, z) -> Ans (FAM (x, y, z))
  | Closure.FAbs (x) -> Ans (FAbs (x))
  | Closure.Sqrt (x) -> Ans (Sqrt (x))
  | Closure.ToFloat (x) -> Ans (ToFloat (x))
  | Closure.ToInt (x) -> Ans (ToInt (x))
  | Closure.ToArray (x) -> Ans (ToArray (x))
  | Closure.In -> Ans (In)
  | Closure.Out (x) -> Ans (Out (x))
  | Closure.Count -> Ans (Count)
  | Closure.ShowExec -> Ans (ShowExec)
  | Closure.SetCurExec -> Ans (SetCurExec)
  | Closure.GetExecDiff -> Ans (GetExecDiff)
  | Closure.GetHp -> Ans (GetHp)
  | Closure.SetHp (x) -> Ans (SetHp (x))
  | Closure.If (c, x, y, e1, e2) -> 
     (match M.find x env with
	    | Type.Bool | Type.Int -> Ans (If (c, x, V (y), g env e1, g env e2))
	    | Type.Float -> Ans (IfF (c, x, y, g env e1, g env e2))
	    | _ -> failwith "comparition supported only for bool, int, and float")
  | Closure.Let ((x, t1), e1, e2) ->
     let e1' = g env e1 in
     let e2' = g (M.add x t1 env) e2 in
	   concat e1' (x, t1) e2'
  | Closure.Var (x) ->
     (match M.find x env with
	    | Type.Unit -> Ans (Nop)
	    | Type.Float -> Ans (FMr (x))
	    | _ -> Ans (Mr (x)))
  | Closure.MakeCls ((x, t), {Closure.entry = l; Closure.actual_fv = ys}, e2) ->
     (* closure のアドレスをセットしてからストア *)
     let e2' = g (M.add x t env) e2 in
     let (offset, store_fv) = 
	     expand
	       (List.map (fun y -> (y, M.find y env)) ys)
	       (1, e2')
	       (fun y _ offset store_fv -> seq (Stw (y, x, C (offset)), store_fv)) in
	   Let ((x, t), Mr (reg_hp), 
	        Let ((reg_hp, Type.Int), Add (reg_hp, C (align offset)), 
	             let z = Id.genid "l" in  
	             Let ((z, Type.Int), SetL(l), 
		                seq (Stw (z, x, C (0)), store_fv))))
  | Closure.AppCls (x, ys) ->
     Ans (CallCls (x, ys))
  | Closure.AppDir (Id.L(x), ys) ->
     Ans (CallDir (Id.L(x), ys))
  | Closure.Tuple (xs) -> (* 組の生成 *)
     let y = Id.genid "t" in
     let (offset, store) = 
	     expand
	       (List.map (fun x -> (x, M.find x env)) xs)
	       (0, Ans (Mr (y)))
	       (fun x _ offset store -> seq (Stw (x, y, C (offset)), store))  in
     Let ((y, Type.Tuple (List.map (fun x -> M.find x env) xs)), Mr (reg_hp),
	  Let ((reg_hp, Type.Int), Add (reg_hp, C (align offset)), store))
  | Closure.LetTuple (xts, y, e2) ->
     let s = Closure.fv e2 in
     let (offset, load) = 
	     expand
	       xts
	       (0, g (M.add_list xts env) e2)
	       (fun x t offset load ->
	        if not (S.mem x s) then load 
	        else Let ((x, t), Ldw (y, C (offset)), load)) in
	   load
  | Closure.Get (x, y) -> (* 配列の読み出し *)
     (match M.find x env with
     | Type.Array (Type.Unit) -> Ans (Nop)
     | Type.Array (_) ->
	Ans (Ldw (x, V (y)))
     | _ -> assert false)
  | Closure.Put (x, y, z) ->
     (match M.find x env with
     | Type.Array (Type.Unit) -> Ans (Nop)
     | Type.Array (_) ->
	Ans (Stw (z, x, V (y)))
     | _ -> assert false)
  | Closure.ExtArray (Id.L(x)) -> Ans(SetL(Id.L("min_caml_" ^ x)))

(* 関数の仮想マシンコード生成 *)
let h { Closure.name = (Id.L(x), t); Closure.args = yts; 
	Closure.formal_fv = zts; Closure.body = e} =
  let (offset, load) = 
    expand
      zts
      (1, g (M.add x t (M.add_list yts (M.add_list zts M.empty))) e)
      (fun z t offset load -> Let ((z, t), Ldw (reg_cl, C (offset)), load)) in
    match t with
      | Type.Fun (_, t2) ->
	       { name = Id.L(x); args = List.fold_left (fun ys (y, _) -> ys@[y]) [] yts; body = load; ret = t2 }
      | _ -> assert false

(* プログラム全体の仮想マシンコード生成 *)
let f (Closure.Prog (fundefs, e)) =
  prerr_endline "generating virtual assembly...";
  data := [];
  let fundefs = List.map h fundefs in
  let e = g M.empty e in
  prerr_endline "virtual assembly generation end";
  Prog (!data, !vars, fundefs, e)
