type closure = { entry : Id.l; actual_fv : Id.t list }
type t = (* クロージャ変換後の式 (caml2html: closure_t) *)
  | Unit
  | Int of int
  | Float of float
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
  | Sqrt of Id.t
  | ToFloat of Id.t
  | ToInt of Id.t
  | ToArray of Id.t
  | In
  | Out of Id.t
  | GetHp
  | SetHp of Id.t
  | IfEq of Id.t * Id.t * t * t
  | IfLE of Id.t * Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | MakeCls of (Id.t * Type.t) * closure * t
  | AppCls of Id.t * Id.t list
  | AppDir of Id.l * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.l
type fundef = { name : Id.l * Type.t;
		            args : (Id.t * Type.t) list;
		            formal_fv : (Id.t * Type.t) list;
		            body : t }
type prog = Prog of fundef list * t

let log = ref ""
    
let rec fv = function
  | Unit | Int(_) | Float(_) | ExtArray(_) | In | GetHp -> S.empty
  | Neg(x) | FNeg(x) | Sqrt(x) | ToFloat(x) | ToInt(x) | ToArray(x) | Out(x) | SetHp(x) -> S.singleton x
  | Add(x, y) | Sub(x, y) | Xor(x, y) | Or(x, y) | And(x, y) | Sll(x, y) | Srl(x, y) | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y) -> S.of_list [x; y]
  | IfEq(x, y, e1, e2)| IfLE(x, y, e1, e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> S.union (fv e1) (S.remove x (fv e2))
  | Var(x) -> S.singleton x
  | MakeCls((x, t), { entry = l; actual_fv = ys }, e) -> S.remove x (S.union (S.of_list ys) (fv e))
  | AppCls(x, ys) -> S.of_list (x :: ys)
  | AppDir(_, xs) | Tuple(xs) -> S.of_list xs
  | LetTuple(xts, y, e) -> S.add y (S.diff (fv e) (S.of_list (List.map fst xts)))
  | Put(x, y, z) -> S.of_list [x; y; z]

let toplevel : fundef list ref = ref []

let rec g env known = function (* クロージャ変換ルーチン本体 (caml2html: closure_g) *)
  | KNormal.Unit -> Unit
  | KNormal.Int(i) -> Int(i)
  | KNormal.Float(d) -> Float(d)
  | KNormal.Neg(x) -> Neg(x)
  | KNormal.Add(x, y) -> Add(x, y)
  | KNormal.Sub(x, y) -> Sub(x, y)
  | KNormal.Xor(x, y) -> Xor(x, y)
  | KNormal.Or(x, y) -> Or(x, y)
  | KNormal.And(x, y) -> And(x, y)
  | KNormal.Sll(x, y) -> Sll(x, y)
  | KNormal.Srl(x, y) -> Srl(x, y)
  | KNormal.FNeg(x) -> FNeg(x)
  | KNormal.FAdd(x, y) -> FAdd(x, y)
  | KNormal.FSub(x, y) -> FSub(x, y)
  | KNormal.FMul(x, y) -> FMul(x, y)
  | KNormal.FDiv(x, y) -> FDiv(x, y)
  | KNormal.Sqrt(x) -> Sqrt(x)
  | KNormal.ToFloat(x) -> ToFloat(x)
  | KNormal.ToInt(x) -> ToInt(x)
  | KNormal.ToArray(x) -> ToArray(x)
  | KNormal.In(x) -> In
  | KNormal.Out(x) -> Out(x)
  | KNormal.GetHp(x) -> GetHp
  | KNormal.SetHp(x) -> SetHp(x)
  | KNormal.IfEq(x, y, e1, e2) -> IfEq(x, y, g env known e1, g env known e2)
  | KNormal.IfLE(x, y, e1, e2) -> IfLE(x, y, g env known e1, g env known e2)
  | KNormal.Let((x, t), e1, e2) ->
     let e1' = g env known e1 in
     Let((x, t), e1', g (M.add x t env) known e2)
  | KNormal.Var(x) -> Var(x)
  | KNormal.LetRec({ KNormal.name = (x, t); KNormal.args = yts; KNormal.body = e1 }, e2) -> (* 関数定義の場合 (caml2html: closure_letrec) *)
     (* 関数定義let rec x y1 ... yn = e1 in e2の場合は、
	 xに自由変数がない(closureを介さずdirectに呼び出せる)
	と仮定し、knownに追加してe1をクロージャ変換してみる *)
     Format.eprintf "function size of %s is %d@." x (KNormal.size e1);
    Format.eprintf "%!";
    let toplevel_backup = !toplevel in
     let env' = M.add x t env in
     let known' = S.add x known in
     let e1' = g (M.add_list yts env') known' e1 in
     (* 本当に自由変数がなかったか、変換結果e1'を確認する *)
     (* 注意: e1'にx自身が変数として出現する場合はclosureが必要!
        (thanks to nuevo-namasute and azounoman; test/cls-bug2.ml参照) *)
     let fve1' = fv e1' in
     let zs = S.diff fve1' (S.of_list (List.map fst yts)) in
     let known', e1' =
	     if S.is_empty zs then known', e1' else
	       (* 駄目だったら状態(toplevelの値)を戻して、クロージャ変換をやり直す *)
	       (log := !log ^ Format.sprintf "free variable(s) %s found in function %s@." (Id.pp_list (S.elements zs)) x;
	        log := !log ^ Format.sprintf "function %s cannot be directly applied in fact@." x;
	        toplevel := toplevel_backup;
	        let e1' = g (M.add_list yts env') known e1 in
	        known, e1') in
     let zs = S.elements (S.diff (if S.is_empty zs then fve1' else fv e1') (S.add x (S.of_list (List.map fst yts)))) in (* 自由変数のリスト *)
     let zts = List.map (function
                          | z when M.mem z env'  ->
                             (z, M.find z env')
                          | z->
			     Format.eprintf "variable %s not found in function %s@." z x;
			    assert false) zs
     in (* ここで自由変数zの型を引くために引数envが必要 *)
     toplevel := { name = (Id.L(x), t); args = yts; formal_fv = zts; body = e1' } :: !toplevel; (* トップレベル関数を追加 *)
     let e2' = g env' known' e2 in
     if S.mem x (fv e2') then (* xが変数としてe2'に出現するか *)
	MakeCls((x, t), { entry = Id.L(x); actual_fv = zs }, e2') (* 出現していたら削除しない *)
     else
       (log := !log ^ Format.sprintf "eliminating closure(s) %s@." x;
	e2') (* 出現しなければMakeClsを削除 *)
  | KNormal.App(x, ys) when S.mem x known -> (* 関数適用の場合 (caml2html: closure_app) *)
      log := !log ^ Format.sprintf "directly applying %s@." x;
      if List.length ys > 79 then (prerr_int (List.length ys);assert false) else ();
      AppDir(Id.L(x), ys)
  | KNormal.App(f, xs) -> assert false;AppCls(f, xs)
  | KNormal.Tuple(xs) -> Tuple(xs)
  | KNormal.LetTuple(xts, y, e) -> LetTuple(xts, y, g (M.add_list xts env) known e)
  | KNormal.Get(x, y) -> Get(x, y)
  | KNormal.Put(x, y, z) -> Put(x, y, z)
  | KNormal.ExtArray(x) -> ExtArray(Id.L(x))
  | KNormal.ExtFunApp(x, ys) -> AppDir(Id.L("min_caml_" ^ x), ys)

let f e =
  log := "";
  prerr_endline "converting closure...";
  toplevel := [];
  let e' = g M.empty S.empty e in
  let e = Prog(List.rev !toplevel, e')
  in
  prerr_endline !log;
  e
