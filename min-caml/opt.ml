let limit = ref 100

let flag = true

let g s f e =
  prerr_endline s;
  let e' = f e in
  if e <> e' then prerr_endline ("opt:"^s);
  e'
  
let rec f n e = (* 最適化処理をくりかえす (caml2html: main_iter) *)
  if flag then
    let rec iter1 m e = 
      Format.eprintf "iteration %d, %d@." n m;
      if m = 0 then e else
	      let e' = (g "elarg" ElArg.f
                    (g "while" While.f
                       (g "hpalloc" HpAlloc.f
                          (g "constfold" ConstFold.f
                             (g "celm" Celm.h
                                (g "union" Union.f
                                   (g "assoc" Assoc.f
                                      (g "beta" Beta.f e)))))))) in
	      if e = e' then
	        e
	      else
	        iter1 (m - 1) e'
    in
    if n = 0 then e else
      (
        let e' = (g "elim" Elim.f
                    (g "inline" Inline.f
                       (iter1 !limit e))) in
        if e = e' then
	        (prerr_endline "iteration end.";
	         e)
        else
	        f (n - 1) e'
      )
  else
    e
