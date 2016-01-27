(*
let rec test_int_of_float i =
  let _ = generic 901 (int_of_float (i2f i)) i 0 in
  let _ = if i - (i / 10000000) * 10000000 = 0 then
    let _ = print_int (i / 10000000) in
    print_newline ();
  else
    ()
  in
  if i = 1325400063 then
    test_int_of_float 2147483648
  else if i = 3472883711 then
    ()
  else
    test_int_of_float (i + 1)
in
test_int_of_float (-1900000000);
*)

let rec test_float_of_int i =
  let _ = generic 902 (f2i(float_of_int i)) i 0 in
  let _ = if i - (i / 10000000) * 10000000 = 0 then
    let _ = print_int (i / 10000000) in
    print_newline ();
  else
    ()
  in
  if i = 4294967295 then
    ()
  else
    test_float_of_int (i + 1)
in
test_float_of_int 0;
 
