(let rec mul a b =
   let abs_a = if a < 0 then -a else a in
   let abs_b = if b < 0 then -b else b in
   let rec mul_sub x i =
     if i = -1 then 
       x
     else
       if (abs_b land (1 lsl i)) = 0 then
         mul_sub x (i - 1)
       else
          mul_sub (x + (abs_a lsl i)) (i - 1)
   in
   let abs = (mul_sub 0 30) land 2147483647
   in
   if ((a lsr 31) lxor (b lsr 31)) = 0 then
     abs
   else
     -abs);

(let rec div a b =
   let rec div_sub x a b i =
     if i = -1 then
       x
     else
       if (a lsr i) >= b then
         div_sub ((1 lsl i) + x) (a - (b lsl i)) b (i - 1)
       else
         div_sub x a b (i - 1)
   in
   let abs_a = if a < 0 then -a else a in
   let abs_b = if b < 0 then -b else b in
   let abs = (div_sub 0 abs_a abs_b 30) land 2147483647
   in
   if ((a lsr 31) lxor (b lsr 31)) = 0 then
     abs
   else
     -abs);

(let rec print_newline a = output 10);

(let rec print_byte a = output a);

(let rec prerr_byte a = output a);

(let rec read_byte u = input u);

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
      print_int_sub a));

(let rec prerr_int_without_null a =
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
      prerr_int_sub a));


(let rec prerr_int a =
   prerr_int_without_null a;
   prerr_byte 0);

(let rec is_number b =
   (* ２つのifを潰したい *)
   if b >= 48 then
     if b <= 57 then
       true
     else
       false
   else
     false);

(let rec read_int u =
   let rec read_int_sub b x =
     if is_number b then
       read_int_sub (read_byte ()) ((mul x 10) + (b - 48))
     else
       x
   in
   let b = read_byte ()
   in
   if is_number b then
       read_int_sub b 0
   else
     if b = 45 then
       -(read_int_sub (read_byte ()) 0)
     else
       read_int u);

(let rec abs_float i =
   i2f(f2i(i) land 2147483647));

(let rec int_of_float f = 
   let exp = ((f2i(f) lsr 23) land 255) - 127 in
   let fraction = ((f2i(f) lor 8388608) land 16777215)
   in
   let rval = 
     if (23 - exp) > 0 then
       (fraction lsr (23 - exp))
     else
       (fraction lsl (exp - 23))
   in
   let rval = rval land 2147483647 in
   if f >= 0.0 then
     rval
   else
     -rval);

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
     i2f(0)
   else
     let sign = if i > 0 then 0 else 1 in
     let i = if i > 0 then i else -i in
     let top = search_top i in
     if top > 23 then
       i2f((sign lsl 31) + ((top + 127) lsl 23) + ((i lxor (1 lsl top) + ((1 lsl (top - 23)) - 1)) lsr (top - 23)))
     else
       i2f((sign lsl 31) + ((top + 127) lsl 23) + ((i lxor (1 lsl top)) lsl (23 - top))));

(let rec floor i =
   let rec floor_sub i =
     float_of_int(int_of_float i)
   in
   if i >= 0.0 then
     floor_sub i;
   else
     floor_sub (i -. 1.0));

(let rec print_float f =
   let rec print_float_sub f j =
       if j = 0 then
         ()
       else
         (let f = f *. 10.0
          in
          let i = int_of_float f
          in
          print_byte (i + 48);
          let p = f -. (float_of_int i)
          in
          print_float_sub p (j - 1))
   in      
   let f = if f >= 0.0 then f else (print_byte 45; -.f)
   in
   let i = int_of_float f
   in
   print_int i;
   print_byte 46;
   let p = f -. (float_of_int i)
   in
   print_float_sub p 5;
   (*print_byte 0*));

(let rec prerr_float f =
   let rec prerr_float_sub f j =
       if j = 0 then
         ()
       else
         (let f = f *. 10.0
          in
          let i = int_of_float f
          in
          prerr_byte (i + 48);
          let p = f -. (float_of_int i)
          in
          prerr_float_sub p (j - 1))
   in      
   (if f > 0.0 then
      ()
    else
      prerr_byte 45);
   let f = if f > 0.0 then f else -.f
   in
   let i = int_of_float f
   in
   prerr_int_without_null i;
   prerr_byte 46;
   let p = f -. (float_of_int i)
   in
   prerr_float_sub p 5;
   prerr_byte 0);

(let rec read_float u =
   let rec read_float_sub1 b f = 
     if is_number b then
       read_float_sub1 (read_byte ()) ((f *. 10.0) +. (float_of_int (b - 48)))
     else
       if b = 46 then
         let rec read_float_sub2 b f p =
           if is_number b then
             read_float_sub2 (read_byte ()) (f +. p *. (float_of_int (b - 48))) (p *. 0.1)
           else
             f
         in
         read_float_sub2 (read_byte ()) f 0.1
       else
         f
   in 
   let b = read_byte ()
   in
   if is_number b then
     read_float_sub1 b 0.0
   else
     if b = 45 then
       0.0 -. (read_float_sub1 (read_byte ()) 0.0)
     else
       read_float u);

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
   -.i);

(let rec print_char i =
   print_byte i);

(let rec kernel_sin a =
   let a2 = a *. a in
   let a3 = a *. a2 in
   let a5 = a3 *. a2 in
   let a7 = a5 *. a2 in
   a -. 0.16666668 *. a3 +. 0.008332824 *. a5 -. 0.00019587841 *. a7);

(let rec kernel_cos a = 
   let a2 = a *. a in
   let a4 = a2 *. a2 in
   let a6 = a2 *. a4 in
   1.0 -. 0.5 *. a2 +. 0.04166368 *. a4 -. 0.0013695068 *. a6);

(* 最適化 *)
(let rec sin a =
   if a >= 0.0 then
     if a > 6.28318548202514 then
       sin (a -. 6.28318548202514)
     else
       if a < 3.1415927410 then
         if a < 1.5707963705 then
           if a < 0.785398185 then
             kernel_sin a
           else
             kernel_cos (1.5707963705 -. a)
         else
           if a < 2.35619455 then
             kernel_cos (a -. 1.5707963705)
           else
             kernel_sin (3.1415927410 -. a)
       else
        let b = a -. 3.1415927410 in
         if b < 1.5707963705 then
           if b < 0.785398185 then
             0.0 -. kernel_sin b
           else
             0.0 -. kernel_cos (1.5707963705 -. b)
         else
           if b < 2.35619455 then
             0.0 -. kernel_cos (b -. 1.5707963705)
           else
             0.0 -. kernel_sin (3.1415927410 -. b)
    else
      0.0 -. sin (0.0 -. a));

(let rec cos a =
   if a >= 0.0 then
     if a > 6.28318548202514 then
       sin (a -. 6.28318548202514)
     else
       if a < 3.1415927410 then
         if a < 1.5707963705 then
           if a < 0.785398185 then
             kernel_cos a
           else
             kernel_sin (1.5707963705 -. a)
         else
           if a < 2.35619455 then
             0.0 -. kernel_sin (a -. 1.5707963705)
           else
             0.0 -. kernel_cos (3.1415927410 -. a)
       else
        let b = a -. 3.1415927410 in
         if b < 1.5707963705 then
           if b < 0.785398185 then
             0.0 -. kernel_sin b
           else
             0.0 -. kernel_cos (1.5707963705 -. b)
         else
           if b < 2.35619455 then
             kernel_cos (b -. 1.5707963705)
           else
             kernel_sin (3.1415927410 -. b)
    else
      cos (0.0 -. a));
           
(let rec kernel_atan a =
   let a2 = a *. a in
   let a3 = a *. a2 in
   let a5 = a3 *. a2 in
   let a7 = a5 *. a2 in
   let a9 = a7 *. a2 in
   let a11 = a9 *. a2 in
   let a13 = a11 *. a2 in 
   a -. 0.3333333 *. a3 +. 0.2 *. a5 -. 0.142857142 *. a7 +. 0.111111104 *. a9 -. 0.08976446 *. a11 +. 0.060035485 *. a13);

(let rec atan a = 
   if a > 0.0 then
     if a < 0.4375 then
       kernel_atan a
     else
       if a < 2.4375 then
         0.78539818 +. kernel_atan ((a -. 1.0) /. (a +. 1.0))
       else
         1.57079637 -. kernel_atan (1.0 /. a)
   else
    let b = 0.0 -. a in
     if b < 0.4375 then
       0.0 -. (kernel_atan b)
     else
       if b < 2.4375 then
         0.0 -. (0.78539818 +. kernel_atan ((b -. 1.0) /. (b +. 1.0)))
       else
         0.0 -. (1.57079637 -. kernel_atan (1.0 /. b)));

(let rec create_array_base n i =
   let hp = get_hp () in
   let hp_a = i2ia(hp) in
   set_hp (hp + n);
   let rec create_array_sub c =
     if c = 0 then
       hp_a.(c) <- i
     else
       (hp_a.(c) <- i;
	      create_array_sub (c - 1))
   in
   create_array_sub n;
   hp_a);

(let rec create_float_array_base n i = i2fa(a2i(create_array_base n (f2i(i)))));
