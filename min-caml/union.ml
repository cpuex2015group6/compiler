(* 最適化パターンの登録と実行 *)

open KNormal

exception Unmatched

let check env x f c = try f (M.find x env) with | Unmatched | Not_found -> c ()
let fail = (fun _ -> raise Unmatched)

let rec get_val = function
  | If(_, _, _, e1, e2) ->
     (match get_val e1, get_val e2 with
     | Int(x), Int(y) when x = y -> Int(x)
     | _ -> raise Unmatched)
  | While(_, _, _, e) ->
     (match get_val e with
     | Int(_) as e -> e
     | _ -> raise Unmatched)
  | Let(_, e1, e2) -> get_val e2
  | LetRec(_, e2) -> get_val e2
  | LetTuple(_, _, e) -> get_val e
  | e -> e
  
let rec rm_val = function
  | If(c, x, y, e1, e2) ->
     If(c, x, y, rm_val e1, rm_val e2)
  | While(x, ys, zs, e) ->
     While(x, ys, zs, rm_val e)
  | Let(xt, e1, e2) -> Let(xt, e1, rm_val e2)
  | LetRec(f, e) -> LetRec(f, rm_val e)
  | LetTuple(xts, t, e) -> LetTuple(xts, t, rm_val e)
  | Int(x) -> Unit
  | e -> raise Unmatched
  
let pat = [
  (fun env -> function
  | If(2, x, y, Int(1), Int(0)) ->
     check env x (fun e -> match e with
     | If(c', x', y', e1', e2') ->
	check env y (fun e -> match e with
	| Int(0) -> If(negcond c', x', y', e1', e2')
	| _ -> raise Unmatched
	) fail
     | _ -> raise Unmatched) fail
  | _ -> raise Unmatched);
  (fun env -> function
  | If(2, x, y, Int(1), Int(0)) ->
     check env y (fun e -> match e with
     | If(c', x', y', e1', e2') ->
	check env x (fun e -> match e with
	| Int(0) -> If(negcond c', x', y', e1', e2')
	| _ -> raise Unmatched
	) fail
     | _ -> raise Unmatched) fail
  | _ -> raise Unmatched);
  (fun env -> function
  | If(2, x, y, Int(1), Int(0)) ->
     check env x (fun e -> match e with
     | If(c', x', y', e1', e2') ->
	check env y (fun e -> match e with
	| Int(1) -> If(c', x', y', e1', e2')
	| _ -> raise Unmatched
	) fail
     | _ -> raise Unmatched) fail
  | _ -> raise Unmatched);
  (fun env -> function
  | If(2, x, y, Int(1), Int(0)) ->
     check env y (fun e -> match e with
     | If(c', x', y', e1', e2') ->
	check env x (fun e -> match e with
	| Int(1) -> If(c', x', y', e1', e2')
	| _ -> raise Unmatched
	) fail
     | _ -> raise Unmatched) fail
  | _ -> raise Unmatched);
  (fun env -> function
  | If(c, x, y, e1, e2) ->
     let e1v = get_val e1 in
     let e2v = get_val e2 in
     (match e1v, e2v with
     | Int(0), Int(1) ->
	If(negcond c, x, y, e2, e1)
     | _ -> raise Unmatched)
  | _ -> raise Unmatched);
  (fun env -> function
  | If(_, _, _, Unit, Unit) ->
     Unit
  | _ -> raise Unmatched);
  (fun env -> function
  | If(c, x, y, Unit, e2) ->
     If(negcond c, x, y, e2, Unit)
  | _ -> raise Unmatched);
  (fun env -> function
  | If(c, x, y, e1, e2) ->
     let e1v = get_val e1 in
     let e2v = get_val e2 in
     (match e1, e2, e1v, e2v with
     | Int(1), Int(0), _, _ ->
	raise Unmatched
     | Int(1), _, _, Int(0) ->
	Let((Id.genid "t", Type.Unit), If(c, x, y, rm_val e1, rm_val e2), If(c, x, y, Int(1), Int(0)))
     | _, Int(0), Int(1), _ ->
	Let((Id.genid "t", Type.Unit), If(c, x, y, rm_val e1, rm_val e2), If(c, x, y, Int(1), Int(0)))
     | _ -> raise Unmatched)
  | _ -> raise Unmatched)
]

let h env e =
  match List.fold_left (fun a p ->
    match a with
    | Some e -> (try Some (p env e) with Unmatched -> Some e)
    | None -> (try Some (p env e) with Unmatched -> None)) None pat with
  | Some x -> x
  | None -> e
  
let rec g env = function
  | If(c, x, y, e1, e2) ->
     let e1 = g env e1 in
     let e2 = g env e2 in
     h env (If(c, x, y, e1, e2))
  | While(x, ys, zs, e) ->
     let e = g env e in
     h env (While(x, ys, zs, e))
  | Let((x, t), e1, e2) ->
     let e1 = g env e1 in
     let e2 = g (M.add x e1 env) e2 in
     h env (Let((x, t), e1, e2))
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
     let e1 = g env e1 in
     let e2 = g env e2 in
     h env (LetRec({ name = xt; args = yts; body = e1 }, e2))
  | LetTuple(xts, y, e) ->
     let e = g env e in
     h env (LetTuple(xts, y, e))
  | e -> h env e

let f = g M.empty
