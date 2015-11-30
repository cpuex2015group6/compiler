open KNormal

exception Unmatched

let check env x f c = try f (M.find x env) with | Unmatched | Not_found -> c ()
  
let pat = [
  (*(fun env -> function
  | FAdd(x, y) ->
     check env x (fun e -> match e with
     | FMul(z, w) -> FAM(z, w, y)
     | _ -> raise Unmatched)
       (fun _ -> check env y (fun e -> match e with
       | FMul(z, w) -> FAM(z, w, x)
       | _ -> raise Unmatched) (fun _ -> raise Unmatched))
  | _ -> raise Unmatched);*)
  (fun env -> function
  | FAbs(x) ->
     check env x (fun e -> match e with
     | FAdd(y, z) -> FAbA(y, z)
     | ToInt(x) ->
	check env x (fun e -> match e with
	| FAdd(y, z) -> FAbA(y, z)
	| _ -> raise Unmatched) (fun _ -> raise Unmatched)
     | _ -> raise Unmatched)
       (fun _ -> raise Unmatched)
  | _ -> raise Unmatched)
]

let h env e =
  match List.fold_left (fun a p ->
    match a with
    | Some _ -> a
    | None -> try Some (p env e) with Unmatched -> None) None pat with
  | Some x -> x
  | None -> e
  
let rec g env = function
  | If(c, x, y, e1, e2) ->
     let e1 = g env e1 in
     let e2 = g env e2 in
     If(c, x, y, e1, e2)
  | Let((x, t), e1, e2) ->
     let e1 = g env e1 in
     let e2 = g (M.add x e1 env) e2 in
     Let((x, t), e1, e2)
  | LetRec({ name = xt; args = yts; body = e1 }, e2) ->
     let e1 = g env e1 in
     let e2 = g env e2 in
     LetRec({ name = xt; args = yts; body = e1 }, e2)
  | LetTuple(xts, y, e) ->
     let e = g env e in
     LetTuple(xts, y, e)
  | e -> h env e

let f = g M.empty
