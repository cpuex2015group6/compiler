(let rec print_newline a = out 0);

(let rec print_byte a = out a);

(let rec prerr_byte a = out a);

(let rec read_byte u = in u);

(let rec print_int a =
   let rec print_int_sub a =
     if a < 10 then
       print_byte (a + 48)
     else
       (print_int_sub (div a 10);
        print_byte (a - (mul (div a 10) 10) + 48))
   in
   (if a < 0 then
      (print_byte 45;
       print_int_sub (-a))
    else
      print_int_sub a);
   print_byte 0);

(let rec prerr_int a =
   let rec prerr_int_sub a =
     if a < 10 then
       prerr_byte (a + 48)
     else
       (prerr_int_sub (div a 10);
        prerr_byte (a - (mul (div a 10) 10) + 48))
   in
   (if a < 0 then
      (prerr_byte 45;
       prerr_int_sub (-a))
    else
      prerr_int_sub a);
   prerr_byte 0);

(let rec read_int u =
   let rec read_int_sub x =
     let b = read_byte ()
     in
     if b = 0 then
       0
     else
       read_int_sub ((mul x 10) + (b - 48))
   in
   read_int_sub 0);

(let rec abs_float i =
   Float(Int(i) land 2147483647));

(let rec floor i =
   let exp = ((Int(i) lsr 23) land 255) - 127 in
   Float((Int(i) lsr (23 - exp)) lsl (23 - exp)));

(let rec int_of_float i =
   let exp = ((Int(i) lsr 23) land 255) - 127 in
   let rval = (((Int(i) lor 8388608) land 16777215) lsr (23 - exp)) in
   rval lor (Int(i) land 2147483648));

(let rec truncate i =
   int_of_float i);

(let rec float_of_int i =
   let rec search_top i = 
     if i = 1 then
       0
     else
       (search_top (i lsr 1)) + 1
   in
   if i = 0 then
     Float(0)
   else
     let sign = if i > 0 then 0 else 1 in
     let top = search_top i in
     Float((sign lsl 31) + ((top + 127) lsl 23) + ((i lxor (1 lsl top)) lsl (23 - top))));

(let rec read_float u =
   let rec read_float_sub1 f = 
     let b = read_byte ()
     in
     if b = 0 then
       0.0
     else
       if b = 46 then
         let rec read_float_sub2 f p =
           let b = read_byte ()
           in
           if b = 0 then
             0.0
           else
             read_float_sub2 (f +. p *. (float_of_int (b - 48))) (p *. 0.1)
         in
         read_float_sub2 f 0.1
       else
         read_float_sub1 ((f *. 10.0) +. (float_of_int (b - 48)))
   in 
   read_float_sub1 0.0);

(let rec fispos x =
  x > 0.0);
         
(let rec fisneg x =
  x < 0.0);

(let rec fiszero x =
   x = 0.0);

(let rec fhalf x =
   x *. 0.5);

(let rec fsqr x =
   x *. x);

(let rec fabs f =
   abs_float f);

(let rec fneg i =
   Float(Int(i) lxor 2147483648));

(let rec print_char i =
   print_byte i);
   

