(let rec mul a b =
   let rec mul_sub a b i =
     if i = -1 then 
       0
     else
       if (b land (1 lsl i)) = 0 then
         mul_sub a b (i - 1)
       else
         (a lsl i) + (mul_sub a b (i - 1))
   in
   mul_sub a b 31);

(let rec div a b =
   let rec div_sub a b i =
     if i = -1 then
       0
     else
       if (a lsr i) >= b then
         (1 lsl i) + div_sub (a - (b lsl i)) b (i - 1)
       else
         div_sub a b (i - 1)
   in
   div_sub a b 31);

(let rec print_newline a = out 10);

(let rec print_byte a = out a);

(let rec prerr_byte a = out a);

(let rec read_byte u = in u);

(let rec print_int_without_null a =
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


(let rec print_int a =
   print_int_without_null a;
   print_byte 0);

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

(let rec read_int u =
   let rec read_int_sub x =
     let b = read_byte ()
     in
     if b = 0 then
       x
     else
       read_int_sub ((mul x 10) + (b - 48))
   in
   read_int_sub 0);

(let rec abs_float i =
   Float(Int(i) land 2147483647));

(let rec floor i =
   let exp = ((Int(i) lsr 23) land 255) - 127 in
   Float((Int(i) lsr (23 - exp)) lsl (23 - exp)));

(let rec int_of_float i= 
   let exp = ((Int(i) lsr 23) land 255) - 127 in
   let rval = (((Int(i) lor 8388608) land 16777215) lsr (23 - exp)) in
   if(i>=0.0) then
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
     Float(0)
   else
     let sign = if i > 0 then 0 else 1 in
     let i = if i > 0 then i else -i in
     let top = search_top i in
     Float((sign lsl 31) + ((top + 127) lsl 23) + ((i lxor (1 lsl top)) lsl (23 - top))));

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
   let f = if f > 0.0 then f else -.f
   in
   (if f > 0.0 then
      print_byte 45;
    else
      ());
   let i = int_of_float f
   in
   print_int_without_null i;
   print_byte 46;
   let p = f -. (float_of_int i)
   in
   print_float_sub p 5;
   print_byte 0);

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
   let f = if f > 0.0 then f else -.f
   in
   (if f > 0.0 then
      prerr_byte 45;
    else
      ());
   let i = int_of_float f
   in
   prerr_int_without_null i;
   prerr_byte 46;
   let p = f -. (float_of_int i)
   in
   prerr_float_sub p 5;
   prerr_byte 0);

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

(let rec kernel_sin a =
   let a3 = a *. a *. a in
   let a5 = a3 *. a *. a in
   let a7 = a5 *. a *. a in
   a -. 0.16666668 *. a3 +. 0.008332824 *. a5 -. 0.00019587841 *. a7);

(let rec kernel_cos a = 
   let a2 = a *. a in
   let a4 = a2 *. a2 in
   let a6 = a2 *. a4 in
   1.0 -. 0.5 *. a2 +. 0.04166368 *. a4 -. 0.0013695068 *. a6);

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

(* 型推論の関係で、create_arrayとして直接呼ぶ事はできない *)
(let rec create_array_base n i =
   let hp = get_hp ()
   in
   let rec create_array_sub n i =
     if n = 0 then
       ()
     else
       ((Array (get_hp ())).(0) <- i; 
        (set_hp ((get_hp ()) + 4);
         create_array_sub (n - 1) i))
   in
   create_array_sub n i;
   hp);

(let rec create_float_array_base n i =
   let hp = get_hp ()
   in
   let rec create_array_sub n i =
     if n = 0 then
       ()
     else
       ((Array (get_hp ())).(0) <- Int(i);
        set_hp ((get_hp ()) + 4);
        create_array_sub (n - 1) i)
   in
   create_array_sub n i;
   hp);
