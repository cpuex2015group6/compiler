(* common subexpression elimination 共通部分式削除を行う *)

open KNormal



let rec search history e =
  match history with
    | [] -> e
    | (v, e1)::xs ->
       match e1 with
         | App(_) -> e
         | _  when e1 = e ->
            Var(v)
         | _ ->
            search xs e

let rec g history e =
  match e with
  | IfEq(e1, e2, t1, t2) ->
     let nt1 = g history t1 in
     let nt2 = g history t2 in
     IfEq(e1, e2, nt1, nt2)
  | IfLE(e1, e2, t1, t2) ->
     let nt1 = g history t1 in
     let nt2 = g history t2 in
     IfLE(e1, e2, nt1, nt2)
  | Let((e, t), t1, t2) ->
     let nt1 = g history t1 in
     let nt2 = g ((e,nt1)::history) t2 in
     Let((e, t), nt1, nt2)
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
     let ne1 = g history e1 in
     let ne2 = g history e2 in
     LetRec({ name = (x, t); args = yts; body = ne1 }, ne2)
  | LetDef({ name = (x, t); args = yts; body = e1 }) ->
     let ne1 = g history e1 in
     LetDef({ name = (x, t); args = yts; body = ne1 })
  | LetTuple(xts, e1, e2) ->
     (* 手抜き　本当はxtsもhistoryに追加すべき *)
     let ne2 = g history e2 in
     LetTuple(xts, e1, ne2)
  | _ ->
     search history e

let f e =
  g [] e
