(* 最適化パターンの登録と実行 *)

open KNormal

exception Unmatched

let check env x f c = try f (M.find x env) with | Unmatched | Not_found -> c ()
let fail = (fun _ -> raise Unmatched)

let rec get_val = function
  | If(_, _, _, e1, e2) ->
     (match get_val e1, get_val e2 with
     | Int(x), Int(y) when x = y -> Int(x)
     | _ -> Unit)
  | Let(_, e1, e2) -> get_val e2
  | LetRec(_, e2) -> get_val e2
  | LetTuple(_, _, e) -> get_val e
  | e -> e
  
  
let pat = [
  (*(fun env -> function
  | FAdd(x, y) ->
     check env x (fun e -> match e with
     | FMul(z, w) -> FAM(z, w, y)
     | _ -> raise Unmatched)
       (fun _ -> check env y (fun e -> match e with
       | FMul(z, w) -> FAM(z, w, x)
       | _ -> raise Unmatched) fail)
  | _ -> raise Unmatched);*)
  (fun env -> function
  | FAbs(x) ->
     check env x (fun e -> match e with
     | FAdd(y, z) -> FAbA(y, z)
     | ToInt(x) ->
	check env x (fun e -> match e with
	| FAdd(y, z) -> FAbA(y, z)
	| _ -> raise Unmatched) fail
     | _ -> raise Unmatched) fail
  | _ -> raise Unmatched);
  (fun env -> function
  | If(c, x, y, e1, e2) as exp ->
     let e1v = get_val e1 in
     let e2v = get_val e2 in
     (match e1v, e2v with
     | Int(0), Int(1) ->
	If(KNormal.negcond c, x, y, e2, e1)
     | _ -> exp)
  | _ -> raise Unmatched)
(* TODO If(Unit,) *)
(* TODO let bool = If(); If(bool){}{} *)
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
