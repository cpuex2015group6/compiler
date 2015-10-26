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
   print_byte 0
 in
 ());

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
   prerr_byte 0
 in
 ());

(let rec read_int u =
   let rec read_int_sub x =
     let b = read_byte ()
     in
     if b = 0 then
       0
     else
       read_int_sub ((mul x 10) + (b - 48))
   in
   read_int_sub 0
 in
 ());

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
             read_float_sub2 (f +. p *. (int_of_float (b - 48))) (p *. 0.1)
         in
         read_float_sub2 f 0.1
       else
         read_float_sub1 ((f *. 10.0) +. (int_of_float (b - 48)))
   in 
   read_float_sub1 0.0
 in
 ());

(let rec abs_float i =
   Float(i land Int(2147483647))
 in
 ());

(let rec floor i =
   let exp = ((Int(i) lsr 23) land 255) - 127 in
   Float((Int(i) lsr (23 - exp)) lsl (23 - exp))
 in
 ());

(let rec int_of_float i =
   let exp = ((Float(i) lsr 23) land 255) - 127 in
   let rval = (((Float(i) lor 8388608) land 16777215) lsr (23 - exp)) in
   Int(rval lor (Float(i) land 2147483648))
 in
 ());

(let rec truncate i =
   int_of_float i
 in
 ());

(let rec float_of_int i =
   let rec search_top i = 
     if i = 1 then
       hoge ()
     else
       (search_top (i lsr 1)) + 1
   in
   if i = 0 then
     Float(0)
   else
     let sign = if i > 0 then 0 else 1 in
     let top = search_top i in
     Float((sign lsl 31) + ((top + 127) lsl 23) + ((i lxor (1 lsl top)) lsl (23 - top)))
 in
 ());

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
   div_sub a b 31
 in
 ());

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
   mul_sub a b 31
 in
 ());
(*
external (=) : int -> int -> bool = "%equal"
external (<>) : int -> int -> bool = "%notequal"
external (<) : int -> int -> bool = "%lessthan"
external (>) : int -> int -> bool = "%greaterthan"
external (<=) : int -> int -> bool = "%lessequal"
external (>=) : int -> int -> bool = "%greaterequal"

external (+) : int -> int -> int = "%addint"
external (-) : int -> int -> int = "%subint"
external ( * ) : int -> int -> int = "%mulint"
external (/) : int -> int -> int = "%divint"

external fequal : float -> float -> bool = "%equal"
external fless : float -> float -> bool = "%lessthan"

val fispos : float -> bool
val fisneg : float -> bool
val fiszero : float -> bool

external (+.) : float -> float -> float = "%addfloat"
external (-.) : float -> float -> float = "%subfloat"
external ( *. ) : float -> float -> float = "%mulfloat"
external (/.) : float -> float -> float = "%divfloat"

external xor : bool -> bool -> bool = "%notequal"
external not : bool -> bool = "%boolnot"

(* runtime routines which should be provided by user-written library *)
external fabs : float -> float = "%absfloat"
external fneg : float -> float = "%negfloat"
val fsqr : float -> float
val fhalf : float -> float
 *)

(let rec fabs f =
   abs_float i
 in
 ());

(let rec abs_float i =
   Float(i land Int(2147483647))
 in
 ());


(let rec print_char i =
   print_byte i
 in
 ());
