(* translation into PowerPC assembly (infinite number of virtual registers) *)

open Asm

let data = ref [] (* 浮動小数点数の定数テーブル *)

let classify xts ini addf addi =
  List.fold_left
    (fun acc (x, t) -> match t with
       | Type.Unit -> acc
       | Type.Float -> addf acc x
       | _ -> addi acc x t) ini xts

let separate xts = 
  classify 
    xts 
    ([], []) 
    (fun (int, float) x -> (int, float @ [x]))
    (fun (int, float) x _ -> (int @ [x], float))

let expand xts ini addf addi = 
  classify
    xts
    ini
    (fun (offset, acc) x -> let offset = align offset in
       (offset + 8, addf x offset acc))
    (fun (offset, acc) x t -> (offset + 4, addi x t offset acc))

let rec g env = function (* 式の仮想マシンコード生成 *)
  | Closure.Unit -> Ans (Nop)
  | Closure.Int (i) -> Ans (Li (i))
  | Closure.Float (d) -> 
     let l = 
	     try
	       let (l, _) = List.find (fun (_, d') -> d = d') !data in
	       l
	     with Not_found ->
	       let l = Id.L (Id.genid "l") in
	       data := (l, d) :: !data;
	       l in
	   Ans (FLi (l))
  | Closure.Neg (x) ->
     let y = Id.genid "t" in
     Let((y, Type.Int), Li (0), Ans(Sub(y, V(x))))
  | Closure.Add (x, y) -> Ans (Add (x, V (y)))
  | Closure.Sub (x, y) -> Ans (Sub (x, V (y)))
  | Closure.Xor (x, y) -> Ans (Xor (x, V (y)))
  | Closure.Or (x, y) -> Ans (Or (x, V (y)))
  | Closure.And (x, y) -> Ans (And (x, V (y)))
  | Closure.Sll (x, y) -> Ans (Sll (x, V (y)))
  | Closure.Srl (x, y) -> Ans (Srl (x, V (y)))
  | Closure.FNeg (x) ->
     let y = Id.genid "t" in
     Let((y, Type.Float), Li (0x80000000), Ans(Xor(x, V(y))))
  | Closure.FAdd (x, y) -> Ans (FAdd (x, y))
  | Closure.FSub (x, y) ->
     let z = Id.genid "t" in
     let w = Id.genid "t" in
     Let((z, Type.Float), Li (0x80000000), Let((w, Type.Float), Xor(y, V(z)), Ans(FAdd(x, w))))
  | Closure.FMul (x, y) -> Ans (FMul (x, y))
  | Closure.FDiv (x, y) -> Ans (FDiv (x, y))
  | Closure.Sin (x) -> Ans (Sin (x))
  | Closure.Cos (x) -> Ans (Cos (x))
  | Closure.Atan (x) -> Ans (Atan (x))
  | Closure.Sqrt (x) -> Ans (Sqrt (x))
  | Closure.IfEq (x, y, e1, e2) -> 
     (match M.find x env with
	    | Type.Bool | Type.Int -> Ans (IfEq (x, V (y), g env e1, g env e2))
	    | Type.Float -> Ans (IfFEq (x, y, g env e1, g env e2))
	    | _ -> failwith "equality supported only for bool, int, and float")
  | Closure.IfLE (x, y, e1, e2) ->
     (match M.find x env with
	    | Type.Bool | Type.Int -> Ans (IfLE (x, V (y), g env e1, g env e2))
	    | Type.Float -> Ans (IfFLE (x, y, g env e1, g env e2))
	    | _ -> failwith "inequality supported only for bool, int, and float")
  | Closure.Let ((x, t1), e1, e2) ->
     let e1' = g env e1 in
     let e2' = g (M.add x t1 env) e2 in
	   concat e1' (x, t1) e2'
  | Closure.Var (x) ->
     (match M.find x env with
	    | Type.Unit -> Ans (Nop)
	    | _ -> Ans (Mr (x)))
  | Closure.MakeCls ((x, t), {Closure.entry = l; Closure.actual_fv = ys}, e2) ->
     (* closure のアドレスをセットしてからストア *)
     let e2' = g (M.add x t env) e2 in
     let (offset, store_fv) = 
	     expand
	       (List.map (fun y -> (y, M.find y env)) ys)
	       (4, e2')
	       (fun y offset store_fv -> seq (Stw (y, x, C (offset)), store_fv))
	       (fun y _ offset store_fv -> seq (Stw (y, x, C (offset)), store_fv)) in
	   Let ((x, t), Mr (reg_hp), 
	        Let ((reg_hp, Type.Int), Add (reg_hp, C (align offset)), 
	             let z = Id.genid "l" in  
	             Let ((z, Type.Int), SetL(l), 
		                seq (Stw (z, x, C (0)), store_fv))))
  | Closure.AppCls (x, ys) ->
     let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
	   Ans (CallCls (x, int, float))
  | Closure.AppDir (Id.L(x), ys) ->
     let (int, float) = separate (List.map (fun y -> (y, M.find y env)) ys) in
	   Ans (CallDir (Id.L(x), int, float))
  | Closure.Tuple (xs) -> (* 組の生成 *)
     let y = Id.genid "t" in
     let (offset, store) = 
	     expand
	       (List.map (fun x -> (x, M.find x env)) xs)
	       (0, Ans (Mr (y)))
	       (fun x offset store -> seq (Stw (x, y, C (offset)), store))
	       (fun x _ offset store -> seq (Stw (x, y, C (offset)), store))  in
	   Let ((y, Type.Tuple (List.map (fun x -> M.find x env) xs)), Mr (reg_hp),
	        Let ((reg_hp, Type.Int), Add (reg_hp, C (align offset)), store))
  | Closure.LetTuple (xts, y, e2) ->
     let s = Closure.fv e2 in
     let (offset, load) = 
	     expand
	       xts
	       (0, g (M.add_list xts env) e2)
	       (fun x offset load ->
	        if not (S.mem x s) then load 
	        else fletd (x, Ldw (y, C (offset)), load))
	       (fun x t offset load ->
	        if not (S.mem x s) then load 
	        else Let ((x, t), Ldw (y, C (offset)), load)) in
	   load
  | Closure.Get (x, y) -> (* 配列の読み出し *)
     let offset = Id.genid "o" in  
	   (match M.find x env with
	    | Type.Array (Type.Unit) -> Ans (Nop)
	    | Type.Array (_) ->
	       Let ((offset, Type.Int), Sll (y, C (2)),
		          Ans (Ldw (x, V (offset))))
	    | _ -> assert false)
  | Closure.Put (x, y, z) ->
     let offset = Id.genid "o" in 
	   (match M.find x env with
	    | Type.Array (Type.Unit) -> Ans (Nop)
	    | Type.Array (_) ->
	       Let ((offset, Type.Int), Sll (y, C (2)), 
		          Ans (Stw (z, x, V (offset)))) 
	    | _ -> assert false)
  | Closure.ExtArray (Id.L(x)) -> Ans(SetL(Id.L("min_caml_" ^ x)))

(* 関数の仮想マシンコード生成 *)
let h { Closure.name = (Id.L(x), t); Closure.args = yts; 
	Closure.formal_fv = zts; Closure.body = e} =
  let (int, float) = separate yts in
  let (offset, load) = 
    expand
      zts
      (4, g (M.add x t (M.add_list yts (M.add_list zts M.empty))) e)
      (fun z offset load -> fletd (z, Ldw (reg_cl, C (offset)), load))
      (fun z t offset load -> Let ((z, t), Ldw (reg_cl, C (offset)), load)) in
    match t with
      | Type.Fun (_, t2) ->
	       { name = Id.L(x); args = int; fargs = float; body = load; ret = t2 }
      | _ -> assert false

(* プログラム全体の仮想マシンコード生成 *)
let f (Closure.Prog (fundefs, e)) =
  data := [];
  let fundefs = List.map h fundefs in
  let e = g M.empty e in
    Prog (!data, fundefs, e)
