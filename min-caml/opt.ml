let limit = ref 1000

let rec f n e = (* 最適化処理をくりかえす (caml2html: main_iter) *)
  let rec iter1 m e = 
    Format.eprintf "iteration %d, %d@." n m;
    if m = 0 then e else
      let e' = (ConstFold.f (Assoc.f (Beta.f e))) in
      if e = e' then
	 e
      else
	iter1 (m - 1) e'
  in
  if n = 0 then e else
    let e = Elim.f e in
    let e' = (Elim.f (Inline.f (iter1 !limit e))) in
    if e = e' then
      (prerr_endline "iteration end.";
       e)
    else
      f (n - 1) e'
