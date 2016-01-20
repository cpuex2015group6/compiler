(* customized version of Map *)

module M =
  Map.Make
    (struct
      type t = Id.t
      let compare = compare
    end)
include M

let keys m = M.fold (fun k _ s -> S.add k s) m S.empty
let add_list xys env = List.fold_left (fun env (x, y) -> add x y env) env xys
let add_list2 xs ys env = List.fold_left2 (fun env x y -> add x y env) env xs ys
