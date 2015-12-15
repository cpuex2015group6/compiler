let rec f e =
  let rec iter1 e =
    let e' = (Simm.f (Aunion.f e)) in
    if e = e' then
      e
    else
      iter1 e'
  in
  iter1 e
