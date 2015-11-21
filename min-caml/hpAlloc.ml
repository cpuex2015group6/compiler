open KNormal

let hp = ref (Some 0)

let rec h fenv = function
  | IfEq(_, _, e1, e2) | IfLE(_, _, e1, e2) -> h fenv e1 && h fenv e2
  | Let(_, e1, e2) -> h fenv e1 && h fenv e2
  | LetRec(_, e) -> assert false; h fenv e
  | LetTuple(_, _, e) -> h fenv e
  | SetHp(_) -> false
  | App(x, _) -> (try M.find x fenv with Not_found ->false)
  | ExtFunApp(_) -> false
  | e -> true
  
let rec g env fenv = function
  | IfEq(x, y, e1, e2) -> IfEq(x, y, g env fenv e1, g env fenv e2)
  | IfLE(x, y, e1, e2) -> IfLE(x, y, g env fenv e1, g env fenv e2)
  | Let((x, t), e1, e2) as exp ->
     if !hp = None then
       exp
     else
       let e1' = g env fenv e1 in
       let env =
	 (match e1' with
	 | Int(i) -> (M.add x i env)
	 | _ -> env)
       in
       let e2' = g env fenv e2 in
       Let((x, t), e1', e2')
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) as exp ->
     if !hp = None then
       exp
     else
       LetRec({ name = (x, t); args = yts; body = e1 }, g env (M.add x (h (M.add x true fenv) e1) fenv) e2)
  | LetTuple(xts, y, e) as exp ->
     if !hp = None then
       exp
     else
       LetTuple(xts, y, g env fenv e)
  | Tuple(xs) as exp->
     (match !hp with
     | Some x ->
	hp := Some (x + List.length xs)
     | None -> ());
     exp
  | SetHp(x) as exp when M.mem x env ->
     hp := Some (M.find x env);
    exp
  | GetHp(_) as exp->
     (match !hp with
     | Some x ->
	Format.eprintf "heap pre-allocated at %d@." x;
       Int(x)
     | None -> exp)
  | App(x, _) as exp->
     (try (if M.find x fenv then () else hp := None;)
      with Not_found -> hp := None);
    exp
  | SetHp(_) | ExtFunApp(_) as exp ->
     hp := None;
    exp
  | e -> e

let rec f e =
  hp := Some Asm.heap_start;
  g M.empty M.empty e
