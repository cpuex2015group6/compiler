# print_newline
	.text
	.align	2
	.globl 	min_caml_print_newline
min_caml_print_newline: 
  limm r08, 10
  out r08, 0
  jr  r05, r02, rFF
#	print_int
#let rec print_int a =
#    let rec print_int_sub a =
#      if a < 10 then
#        print_byte (a + 48)
#      else
#        (print_int (div a 10)   ;
#         print_byte (a - (mul (div a 10) 10) + 48))
#    in
#    if a < 0 then
#      print_byte 45             ;
#      print_int_sub (-a)
#    else
#      print_int_sub a           ;
#    print_byte 0
#      in
#      print_int 15
	.text
	.align 	2
	.globl	min_caml_print_int
print_int_sub.print_int:
  limm  r09, 10
  limm  r06, 10
  cmp r07, r08, r06
  limm  r06, jrge_else.print_int54
  jrlt  r05, r07, r06
  limm  r06, 0
  add r05, r03, r06
  stw r05, r09, rFF
  limm  r06, 4
  add r05, r03, r06
  stw r05, r08, rFF
  or  r05, r02, rFF
  limm  r06, 12
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 16
  add r03, r03, r06
  limm  r06, min_caml_div
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 16
  sub r03, r03, r06
  limm  r06, 12
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  or  r05, r02, rFF
  limm  r06, 12
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 16
  add r03, r03, r06
  limm  r06, min_caml_print_int
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 16
  sub r03, r03, r06
  limm  r06, 12
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r06, 4
  add r05, r03, r06
  ldw r08, r05, rFF
  limm  r06, 0
  add r05, r03, r06
  ldw r09, r05, rFF
  or  r05, r02, rFF
  limm  r06, 12
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 16
  add r03, r03, r06
  limm  r06, min_caml_div
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 16
  sub r03, r03, r06
  limm  r06, 12
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r06, 0
  add r05, r03, r06
  ldw r09, r05, rFF
  or  r05, r02, rFF
  limm  r06, 12
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 16
  add r03, r03, r06
  limm  r06, min_caml_mul
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 16
  sub r03, r03, r06
  limm  r06, 12
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r06, 4
  add r05, r03, r06
  ldw r09, r05, rFF
  sub r08, r09, r08
  limm  r06, 48
  add r08, r08, r06
  limm  r06, min_caml_print_byte
  jr  r05, r06, rFF
jrge_else.print_int54:
  limm  r06, 48
  add r08, r08, r06
  limm  r06, min_caml_print_byte
  jr  r05, r06, rFF
min_caml_print_int:
  limm  r06, 0
  cmp r07, r08, r06
  limm  r06, jrge_else.print_int55
  jrlt  r05, r07, r06
  or  r05, r02, rFF
  limm  r06, 4
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 8
  add r03, r03, r06
  limm  r06, print_int_sub.print_int
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 8
  sub r03, r03, r06
  limm  r06, 4
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r06, jrge_cont.print_int56
  jr  r05, r06, rFF
jrge_else.print_int55:
  limm  r09, 45
  limm  r06, 0
  add r05, r03, r06
  stw r05, r08, rFF
  or  r05, r02, rFF
  or  r08, r09, rFF
  limm  r06, 4
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 8
  add r03, r03, r06
  limm  r06, min_caml_print_byte
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 8
  sub r03, r03, r06
  limm  r06, 4
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r08, 0
  limm  r06, 0
  add r05, r03, r06
  ldw r09, r05, rFF
  sub r08, r08, r09
  or  r05, r02, rFF
  limm  r06, 4
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 8
  add r03, r03, r06
  limm  r06, print_int_sub.print_int
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 8
  sub r03, r03, r06
  limm  r06, 4
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
jrge_cont.print_int56:
  limm  r08, 0
  limm  r06, min_caml_print_byte
  jr  r05, r06, rFF
#	print_byte
	.text
	.align 	2
  .globl	min_caml_print_byte
min_caml_print_byte:  
  out r08, 0
  jr  r05, r02, rFF
#	read_byte
	.text
	.align 	2
  .globl	min_caml_read_byte
min_caml_read_byte:  
  in r08, 0
  jr  r05, r02, rFF
#	prerr_int
#let rec print_int a =
#  if a < 10 then
#    print_byte (a + 48);
#    print_byte 0
#  else
#    (print_int (div a 10);
#     print_byte (a - (mul (div a 10) 10) + 48))
#    in
#    print_int 15
	.text
	.align 	2
	.globl	min_caml_prerr_int
min_caml_prerr_int:
  limm  r09, 10
  limm  r06, 10
  cmp r07, r08, r06
  limm  r06, jrge_else.prerr_int
  jrlt  r05, r07, r06
  limm  r06, 0
  add r05, r03, r06
  stw r05, r09, rFF
  limm  r06, 4
  add r05, r03, r06
  stw r05, r08, rFF
  or  r05, r02, rFF
  limm  r06, 12
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 16
  add r03, r03, r06
  limm  r06, min_caml_div
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 16
  sub r03, r03, r06
  limm  r06, 12
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  or  r05, r02, rFF
  limm  r06, 12
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 16
  add r03, r03, r06
  limm  r06, min_caml_prerr_int
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 16
  sub r03, r03, r06
  limm  r06, 12
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r06, 4
  add r05, r03, r06
  ldw r08, r05, rFF
  limm  r06, 0
  add r05, r03, r06
  ldw r09, r05, rFF
  or  r05, r02, rFF
  limm  r06, 12
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 16
  add r03, r03, r06
  limm  r06, min_caml_div
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 16
  sub r03, r03, r06
  limm  r06, 12
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r06, 0
  add r05, r03, r06
  ldw r09, r05, rFF
  or  r05, r02, rFF
  limm  r06, 12
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 16
  add r03, r03, r06
  limm  r06, min_caml_mul
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 16
  sub r03, r03, r06
  limm  r06, 12
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r06, 4
  add r05, r03, r06
  ldw r09, r05, rFF
  sub r08, r09, r08
  limm  r06, 48
  add r08, r08, r06
  limm  r06, min_caml_prerr_byte
  jr  r05, r06, rFF
jrge_else.prerr_int:
  limm  r06, 48
  add r08, r08, r06
  or  r05, r02, rFF
  limm  r06, 12
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 16
  add r03, r03, r06
  limm  r06, min_caml_prerr_byte
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 16
  sub r03, r03, r06
  limm  r06, 12
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r08, 0
  limm  r06, min_caml_prerr_byte
  jr  r05, r06, rFF
#	prerr_byte
	.text
	.align 	2
	.globl	min_caml_prerr_byte
min_caml_prerr_byte:  
  out r08, 0
  jr  r05, r02, rFF
#	prerr_float
	.text
	.align 	2
#	.globl 	min_caml_prerr_float
#	read_int
#let rec read_int x =
#  let b = read_byte ()
#  in
#  if b = 0 then
#    0
#  else
#    let i = b - 48 in
#    let j = if i >= 0 then
#              if i < 10 then
#                i
#              else
#                1
#            else
#              1
#    in
#    div j (read_int ())
#    in
#    print_int (read_int ())
	.text
	.align 	2
	.globl	min_caml_read_int
min_caml_read_int:  
  or  r05, r02, rFF
  limm  r06, 4
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 8
  add r03, r03, r06
  limm  r06, min_caml_read_byte
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 8
  sub r03, r03, r06
  limm  r06, 4
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r06, 0
  cmp r07, r08, r06
  limm  r06, jreq_else.read_int0
  jrneq r05, r07, r06
  limm  r08, 0
  jr  r05, r02, rFF
jreq_else.read_int0:
  limm  r06, 48
  sub r08, r08, r06
  limm  r06, 0
  cmp r07, r08, r06
  limm  r06, jrge_else.read_int1
  jrlt  r05, r07, r06
  limm  r06, 10
  cmp r07, r08, r06
  limm  r06, jrge_else.read_int3
  jrlt  r05, r07, r06
  limm  r08, 1
  limm  r06, jrge_cont.read_int4
  jr  r05, r06, rFF
jrge_else.read_int3:
jrge_cont.read_int4:
  limm  r06, jrge_cont.read_int2
  jr  r05, r06, rFF
jrge_else.read_int1:
  limm  r08, 1
jrge_cont.read_int2:
  limm  r06, 0
  add r05, r03, r06
  stw r05, r08, rFF
  or  r05, r02, rFF
  limm  r06, 4
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 8
  add r03, r03, r06
  limm  r06, min_caml_read_int
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 8
  sub r03, r03, r06
  limm  r06, 4
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r09, r08, rFF
  or  r02, r05, rFF
  limm  r06, 0
  add r05, r03, r06
  ldw r08, r05, rFF
  limm  r06, min_caml_div
  jr  r05, r06, rFF
# 	read_float
	.text
	.align	2
#	.globl	min_caml_read_float
#	create_array
	.text
	.align	2
	.globl	min_caml_create_array
min_caml_create_array:
  or	r09, r08, rFF
	or	r08, r04, rFF
  limm  r06, 2
  sll	r09, r09, r06
  add	r04, r04, r09
  jr	r05, r02, rFF
#	create_float_array
	.text
	.align	2
	.globl	min_caml_create_float_array
min_caml_create_float_array:
  or	r09, r08, rFF
	or	r08, r04, rFF
  limm  r06, 2
  sll	r09, r09, r06
  add	r04, r04, r09
  jr	r05, r02, rFF
#	abs_float
#let rec abs_float i =
#  i land 2147483647
#    in
#    print_int (abs_float 1091567616)
	.text
	.align	2
	.globl	min_caml_abs_float
min_caml_abs_float:
  limm  r09, 32767
  limm  r06, 16
  sll r09, r09, r06
  limm  r06, 65535
  or  r09, r09, r06
  and r08, r08, r09
  jr  r05, r02, rFF
# 	floor
#let rec floor i =
#    let exp = ((i lsr 23) land 255) - 127 in
#    (i lsr (23 - exp)) lsl (23 - exp)
#      in
#      print_int (floor 1075838976)
	.text
	.align 	2
	.globl 	min_caml_floor
min_caml_floor:
  limm  r06, 23
  srl r09, r08, r06
  limm  r0A, 255
  and r09, r09, r0A
  limm  r06, 127
  sub r09, r09, r06
  limm  r0A, 23
  sub r0A, r0A, r09
  srl r08, r08, r0A
  limm  r0A, 23
  sub r09, r0A, r09
  sll r08, r08, r09
  jr  r05, r02, rFF
# int_of_float, truncate
#let rec int_of_float i =
#    let exp = ((i lsr 23) land 255) - 127 in
#    let rval = (((i lor 8388608) land 16777215) lsr (23 - exp)) in
#    rval lor (i land 2147483648)
#      in
#      print_int (int_of_float 1091567616)
	.text
	.align	2
	.globl	min_caml_int_of_float
  .globl  min_caml_truncate
min_caml_truncate:  
min_caml_int_of_float:
  limm  r06, 23
  srl r09, r08, r06
  limm  r0A, 255
  and r09, r09, r0A
  limm  r06, 127
  sub r09, r09, r06
  limm  r0A, 128
  limm  r06, 16
  sll r0A, r0A, r06
  limm  r06, 0
  or  r0A, r0A, r06
  or  r0A, r08, r0A
  limm  r0B, 255
  limm  r06, 16
  sll r0B, r0B, r06
  limm  r06, 65535
  or  r0B, r0B, r06
  and r0A, r0A, r0B
  limm  r0B, 23
  sub r09, r0B, r09
  srl r09, r0A, r09
  limm  r0A, 32768
  limm  r06, 16
  sll r0A, r0A, r06
  limm  r06, 0
  or  r0A, r0A, r06
  and r08, r08, r0A
  or  r08, r09, r08
  jr  r05, r02, rFF
#	float_of_int
#let rec float_of_int i =
#  let rec search_top i = 
#    if i = 1 then
#      0
#    else
#      (search_top (i lsr 1)) + 1
#  in
#  if i = 0 then 0 else
#    let sign = if i > 0 then 0 else 1 in
#    let top = search_top i in
#    (sign lsl 31) + ((top + 127) lsl 23) + ((i lxor (1 lsl top)) lsl (23 - top))
#    in
#    print_int (float_of_int 9)
	.text
	.align	2
	.globl	min_caml_float_of_int
search_top.min_caml_float_of_int:
  limm  r06, 1
  cmp r07, r08, r06
  limm  r06, jreq_else.search_top
  jrneq r05, r07, r06
  limm  r08, 0
  jr  r05, r02, rFF
jreq_else.search_top:
  limm  r06, 1
  srl r08, r08, r06
  or  r05, r02, rFF
  limm  r06, 4
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 8
  add r03, r03, r06
  limm  r06, search_top.min_caml_float_of_int
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 8
  sub r03, r03, r06
  limm  r06, 4
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r06, 1
  add r08, r08, r06
  jr  r05, r02, rFF
min_caml_float_of_int:
  limm  r06, 0
  cmp r07, r08, r06
  limm  r06, jreq_else.min_caml_float_of_int0
  jrneq r05, r07, r06
  limm  r08, 0
  jr  r05, r02, rFF
jreq_else.min_caml_float_of_int0:
  limm  r06, 0
  cmp r07, r08, r06
  limm  r06, jrle_else.min_caml_float_of_int1
  jrgt  r05, r07, r06
  limm  r09, 1
  limm  r06, jrle_cont.min_caml_float_of_int2
  jr  r05, r06, rFF
jrle_else.min_caml_float_of_int1:
  limm  r09, 0
jrle_cont.min_caml_float_of_int2:
  limm  r06, 0
  add r05, r03, r06
  stw r05, r08, rFF
  limm  r06, 4
  add r05, r03, r06
  stw r05, r09, rFF
  or  r05, r02, rFF
  limm  r06, 12
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 16
  add r03, r03, r06
  limm  r06, search_top.min_caml_float_of_int
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 16
  sub r03, r03, r06
  limm  r06, 12
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r06, 4
  add r05, r03, r06
  ldw r09, r05, rFF
  limm  r06, 31
  sll r09, r09, r06
  limm  r06, 127
  add r0A, r08, r06
  limm  r06, 23
  sll r0A, r0A, r06
  add r09, r09, r0A
  limm  r0A, 1
  sll r0A, r0A, r08
  limm  r06, 0
  add r05, r03, r06
  ldw r0B, r05, rFF
  xor r0A, r0B, r0A
  limm  r0B, 23
  sub r08, r0B, r08
  sll r08, r0A, r08
  add r08, r09, r08
  jr  r05, r02, rFF
# div  
#let rec div a b =
#    let rec div_sub a b i =
#      if i = -1 then
#        0
#      else
#        if (a lsr i) >= b then
#          (1 lsl i) + div_sub (a - (b lsl i)) b (i - 1)
#        else
#          div_sub a b (i - 1)
#      in
#      div_sub a b 31
#      in
#      print_int (div 15 2)
	.text
	.align	2
  .globl min_caml_div
div_sub.min_caml_div:
  limm  r06, -1
  cmp r07, r0A, r06
  limm  r06, jreq_else.min_caml_div0
  jrneq r05, r07, r06
  limm  r08, 0
  jr  r05, r02, rFF
jreq_else.min_caml_div0:
  srl r0B, r08, r0A
  cmp r07, r09, r0B
  limm  r06, jrle_else.min_caml_div1
  jrgt  r05, r07, r06
  limm  r0B, 1
  sll r0B, r0B, r0A
  sll r0C, r09, r0A
  sub r08, r08, r0C
  limm  r06, 1
  sub r0A, r0A, r06
  limm  r06, 0
  add r05, r03, r06
  stw r05, r0B, rFF
  or  r05, r02, rFF
  limm  r06, 4
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 8
  add r03, r03, r06
  limm  r06, div_sub.min_caml_div
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 8
  sub r03, r03, r06
  limm  r06, 4
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r06, 0
  add r05, r03, r06
  ldw r09, r05, rFF
  add r08, r09, r08
  jr  r05, r02, rFF
jrle_else.min_caml_div1:
  limm  r06, 1
  sub r0A, r0A, r06
  limm  r06, div_sub.min_caml_div
  jr  r05, r06, rFF
min_caml_div:
  limm  r0A, 31
  limm  r06, div_sub.min_caml_div
  jr  r05, r06, rFF
# mul
#let rec mul a b =
#  let rec mul_sub a b i =
#    if i = -1 then 
#      0
#    else
#      if (b land (1 lsl i)) = 0 then
#        mul_sub a b (i - 1)
#      else
#        (a lsl i) + (mul_sub a b (i - 1))
#    in
#    mul_sub a b 31
#    in
#    print_int (mul 15 9)
	.text
	.align	2
  .globl min_caml_mul
mul_sub.min_caml_mul:
  limm  r06, -1
  cmp r07, r0A, r06
  limm  r06, jreq_else.min_caml_mul0
  jrneq r05, r07, r06
  limm  r08, 0
  jr  r05, r02, rFF
jreq_else.min_caml_mul0:
  limm  r0B, 1
  sll r0B, r0B, r0A
  and r0B, r09, r0B
  limm  r06, 0
  cmp r07, r0B, r06
  limm  r06, jreq_else.min_caml_mul1
  jrneq r05, r07, r06
  limm  r06, 1
  sub r0A, r0A, r06
  limm  r06, mul_sub.min_caml_mul
  jr  r05, r06, rFF
jreq_else.min_caml_mul1:
  sll r0B, r08, r0A
  limm  r06, 1
  sub r0A, r0A, r06
  limm  r06, 0
  add r05, r03, r06
  stw r05, r0B, rFF
  or  r05, r02, rFF
  limm  r06, 4
  add r06, r03, r06
  stw r06, r05, rFF
  limm  r06, 8
  add r03, r03, r06
  limm  r06, mul_sub.min_caml_mul
  or  r05, r06, rFF
  jr  r02, r05, rFF
  limm  r06, 8
  sub r03, r03, r06
  limm  r06, 4
  add r05, r03, r06
  ldw r05, r05, rFF
  or  r02, r05, rFF
  limm  r06, 0
  add r05, r03, r06
  ldw r09, r05, rFF
  add r08, r09, r08
  jr  r05, r02, rFF
min_caml_mul:
  limm  r0A, 31
  limm  r06, mul_sub.min_caml_mul
  jr  r05, r06, rFF
