(* customized version of Set *)

module S =
  Set.Make
    (struct
      type t = Id.t
      let compare = compare
    end)
include S

let of_list l = List.fold_left (fun s e -> add e s) empty l
let sremove rs s = S.fold (fun e s -> if S.mem e rs then s else S.add e s) s S.empty
