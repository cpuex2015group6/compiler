type t = (* MinCamlの型を表現するデータ型 (caml2html: type_t) *)
  | Unit
  | Bool
  | Int
  | Float
  | Fun of t list * t (* arguments are uncurried *)
  | Tuple of t list
  | Array of t
  | Var of t option ref

let gentyp () = Var(ref None) (* 新しい型変数を作る *)

let conv_float f =
  let s = if f >= 0.0 then 0 else 1 in
  let f = abs_float(f) in
  let e, m = if f = 0.0 then 0, 0 else
      let m', e = frexp f in
      let get_man f = int_of_float (ldexp (f -. 0.5) 24) in
      e + 126, get_man m'
  in
  (s lsl 31) + (e lsl 23) + m

let conv_int i =
  if i = 0 then 0.0 else
    let x, _ = frexp (float_of_int ((i land 8388607) lor 8388608)) in
    print_float x;
    let f = ldexp (x *. 2.0) (((i lsr 23) land 255) - 127) in
    if (i land 2147483648) = 0 then
      f
    else
      -.f
