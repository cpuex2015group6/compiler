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
#        (print_int_sub (div a 10)   ;
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
  limm  r06, print_int_sub.print_int
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
#let rec read_int u =
#  let rec read_int_sub x =
#    let b = read_byte ()
#    in
#    if b = 0 then
#      0
#    else
#      read_int_sub ((mul x 10) + (b - 48))
#  in
#  read_int_sub 0
#    in
#    print_int (read_int ())
	.text
	.align 	2
	.globl	min_caml_read_int
read_int_sub.min_caml_read_int15:
  limm  r06, 0
  add r05, r03, r06
  stw r05, r08, r1F
  or  r05, r02, r1F
  limm  r06, 4
  add r06, r03, r06
  stw r06, r05, r1F
  limm  r06, 8
  add r03, r03, r06
  limm  r06, min_caml_read_byte
  or  r05, r06, r1F
  jr  r02, r05, r1F
  limm  r06, 8
  sub r03, r03, r06
  limm  r06, 4
  add r05, r03, r06
  ldw r05, r05, r1F
  or  r02, r05, r1F
  limm  r06, 0
  cmp r07, r08, r06
  limm  r06, jreq_else.min_caml_read_int29
  jrneq r05, r07, r06
  limm  r08, 0
  jr  r05, r02, r1F
jreq_else.min_caml_read_int29:
  limm  r09, 10
  limm  r06, 0
  add r05, r03, r06
  ldw r0A, r05, r1F
  limm  r06, 4
  add r05, r03, r06
  stw r05, r08, r1F
  or  r05, r02, r1F
  or  r08, r0A, r1F
  limm  r06, 12
  add r06, r03, r06
  stw r06, r05, r1F
  limm  r06, 16
  add r03, r03, r06
  limm  r06, min_caml_mul
  or  r05, r06, r1F
  jr  r02, r05, r1F
  limm  r06, 16
  sub r03, r03, r06
  limm  r06, 12
  add r05, r03, r06
  ldw r05, r05, r1F
  or  r02, r05, r1F
  limm  r06, 4
  add r05, r03, r06
  ldw r09, r05, r1F
  limm  r06, 48
  sub r09, r09, r06
  add r08, r08, r09
  limm  r06, read_int_sub.min_caml_read_int15
  jr  r05, r06, r1F
min_caml_read_int:
  limm  r08, 0
  limm  r06, read_int_sub.min_caml_read_int15
  jr  r05, r06, r1F
# 	read_float
#let rec read_float u =
#  let rec read_float_sub1 f = 
#    let b = read_byte ()
#    in
#    if b = 0 then
#      0.0
#    else
#      if b = 46 then
#        let rec read_float_sub2 f p =
#          let b = read_byte ()
#          in
#          if b = 0 then
#            0.0
#          else
#            read_float_sub2 (f +. p *. (int_of_float (b - 48))) (p *. 0.1)
#        in
#        read_float_sub2 f 0.1
#      else
#        read_float_sub1 ((f *. 10.0) +. (int_of_float (b - 48)))
#  in 
#  read_float_sub1 0.0
#    in
#    print_float (read_float ())
  .data
l.min_caml_read_float56:   # 10.000000
  .long 10.000000d
  .align 3
l.min_caml_read_float55:   # 0.000000
  .long 0.000000d
  .align 3
l.min_caml_read_float54:   # 0.100000
  .long 0.100000d
	.text
	.align	2
	.globl	min_caml_read_float
read_float_sub2.min_caml_read_float39:
  limm  r06, 4
  add r06, r17, r06
  ldw r08, r06, r1F
  limm  r06, 0
  add r05, r03, r06
  stw r05, r17, r1F
  limm  r06, 4
  add r05, r03, r06
  stw r05, r18, r1F
  limm  r06, 8
  add r05, r03, r06
  stw r05, r19, r1F
  limm  r06, 12
  add r05, r03, r06
  stw r05, r08, r1F
  or  r05, r02, r1F
  limm  r06, 20
  add r06, r03, r06
  stw r06, r05, r1F
  limm  r06, 24
  add r03, r03, r06
  limm  r06, min_caml_read_byte
  or  r05, r06, r1F
  jr  r02, r05, r1F
  limm  r06, 24
  sub r03, r03, r06
  limm  r06, 20
  add r05, r03, r06
  ldw r05, r05, r1F
  or  r02, r05, r1F
  limm  r06, 12
  add r05, r03, r06
  ldw r09, r05, r1F
  cmp r07, r08, r09
  limm  r06, jreq_else.min_caml_read_float67
  jrneq r05, r07, r06
  limm  r06, l.55
  ldw r18, r06, r1F
  jr  r05, r02, r1F
jreq_else.min_caml_read_float67:
  limm  r06, 48
  sub r08, r08, r06
  or  r05, r02, r1F
  limm  r06, 20
  add r06, r03, r06
  stw r06, r05, r1F
  limm  r06, 24
  add r03, r03, r06
  limm  r06, min_caml_int_of_float
  or  r05, r06, r1F
  jr  r02, r05, r1F
  limm  r06, 24
  sub r03, r03, r06
  limm  r06, 20
  add r05, r03, r06
  ldw r05, r05, r1F
  or  r02, r05, r1F
  limm  r06, 8
  add r05, r03, r06
  ldw r19, r05, r1F
  fmul  r18, r19, r18
  limm  r06, 4
  add r05, r03, r06
  ldw r1A, r05, r1F
  fadd  r18, r1A, r18
  limm  r06, l.54
  ldw r1A, r06, r1F
  fmul  r19, r19, r1A
  limm  r06, 0
  add r05, r03, r06
  ldw r17, r05, r1F
  ldw r16, r17, r1F
  jr  r05, r16, r1F
read_float_sub1.min_caml_read_float27:
  limm  r06, 0
  add r05, r03, r06
  stw r05, r18, r1F
  or  r05, r02, r1F
  limm  r06, 4
  add r06, r03, r06
  stw r06, r05, r1F
  limm  r06, 8
  add r03, r03, r06
  limm  r06, min_caml_read_byte
  or  r05, r06, r1F
  jr  r02, r05, r1F
  limm  r06, 8
  sub r03, r03, r06
  limm  r06, 4
  add r05, r03, r06
  ldw r05, r05, r1F
  or  r02, r05, r1F
  limm  r09, 0
  limm  r06, 0
  cmp r07, r08, r06
  limm  r06, jreq_else.min_caml_read_float68
  jrneq r05, r07, r06
  limm  r06, l.55
  ldw r18, r06, r1F
  jr  r05, r02, r1F
jreq_else.min_caml_read_float68:
  limm  r06, 46
  cmp r07, r08, r06
  limm  r06, jreq_else.min_caml_read_float69
  jrneq r05, r07, r06
  or  r17, r04, r1F
  limm  r06, 8
  add r04, r04, r06
  limm  r08, read_float_sub2.min_caml_read_float39
  limm  r06, 0
  add r06, r17, r06
  stw r06, r08, r1F
  limm  r06, 4
  add r06, r17, r06
  stw r06, r09, r1F
  limm  r06, l.54
  ldw r19, r06, r1F
  limm  r06, 0
  add r05, r03, r06
  ldw r18, r05, r1F
  ldw r16, r17, r1F
  jr  r05, r16, r1F
jreq_else.min_caml_read_float69:
  limm  r06, l.56
  ldw r18, r06, r1F
  limm  r06, 0
  add r05, r03, r06
  ldw r19, r05, r1F
  fmul  r18, r19, r18
  limm  r06, 48
  sub r08, r08, r06
  limm  r06, 4
  add r05, r03, r06
  stw r05, r18, r1F
  or  r05, r02, r1F
  limm  r06, 12
  add r06, r03, r06
  stw r06, r05, r1F
  limm  r06, 16
  add r03, r03, r06
  limm  r06, min_caml_int_of_float
  or  r05, r06, r1F
  jr  r02, r05, r1F
  limm  r06, 16
  sub r03, r03, r06
  limm  r06, 12
  add r05, r03, r06
  ldw r05, r05, r1F
  or  r02, r05, r1F
  limm  r06, 4
  add r05, r03, r06
  ldw r19, r05, r1F
  fadd  r18, r19, r18
  limm  r06, read_float_sub1.min_caml_read_float27
  jr  r05, r06, r1F
min_caml_read_float:
  limm  r06, l.55
  ldw r18, r06, r1F
  limm  r06, read_float_sub1.min_caml_read_float27
  jr  r05, r06, r1F
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
div_sub.min_caml_div23:
  limm  r06, 65535
  limm  r06, 16
  sll r06, r06, r06
  limm  r06, 65535
  or  r06, r06, r06
  cmp r07, r0A, r06
  limm  r06, jreq_else.min_caml_div42
  jrneq r05, r07, r06
  limm  r08, 0
  jr  r05, r02, r1F
  jreq_else.min_caml_div42:
  srl r0B, r08, r0A
  cmp r07, r09, r0B
  limm  r06, jrle_else.min_caml_div43
  jrgt  r05, r07, r06
  limm  r0B, 1
  sll r0B, r0B, r0A
  sll r0C, r09, r0A
  sub r08, r08, r0C
  limm  r06, 1
  sub r0A, r0A, r06
  limm  r06, 0
  add r05, r03, r06
  stw r05, r0B, r1F
  or  r05, r02, r1F
  limm  r06, 4
  add r06, r03, r06
  stw r06, r05, r1F
  limm  r06, 8
  add r03, r03, r06
  limm  r06, div_sub.min_caml_div23
  or  r05, r06, r1F
  jr  r02, r05, r1F
  limm  r06, 8
  sub r03, r03, r06
  limm  r06, 4
  add r05, r03, r06
  ldw r05, r05, r1F
  or  r02, r05, r1F
  limm  r06, 0
  add r05, r03, r06
  ldw r09, r05, r1F
  add r08, r09, r08
  jr  r05, r02, r1F
  jrle_else.min_caml_div43:
  limm  r06, 1
  sub r0A, r0A, r06
  limm  r06, div_sub.min_caml_div23
  jr  r05, r06, r1F
min_caml_div:
  limm  r0A, 31
  limm  r06, div_sub.min_caml_div23
  jr  r05, r06, r1F
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
mul_sub.min_caml_mul23:
  limm  r06, 65535
  limm  r06, 16
  sll r06, r06, r06
  limm  r06, 65535
  or  r06, r06, r06
  cmp r07, r0A, r06
  limm  r06, jreq_else.min_caml_mul42
  jrneq r05, r07, r06
  limm  r08, 0
  jr  r05, r02, r1F
  jreq_else.min_caml_mul42:
  limm  r0B, 1
  sll r0B, r0B, r0A
  and r0B, r09, r0B
  limm  r06, 0
  cmp r07, r0B, r06
  limm  r06, jreq_else.min_caml_mul43
  jrneq r05, r07, r06
  limm  r06, 1
  sub r0A, r0A, r06
  limm  r06, mul_sub.min_caml_mul23
  jr  r05, r06, r1F
  jreq_else.min_caml_mul43:
  sll r0B, r08, r0A
  limm  r06, 1
  sub r0A, r0A, r06
  limm  r06, 0
  add r05, r03, r06
  stw r05, r0B, r1F
  or  r05, r02, r1F
  limm  r06, 4
  add r06, r03, r06
  stw r06, r05, r1F
  limm  r06, 8
  add r03, r03, r06
  limm  r06, mul_sub.min_caml_mul23
  or  r05, r06, r1F
  jr  r02, r05, r1F
  limm  r06, 8
  sub r03, r03, r06
  limm  r06, 4
  add r05, r03, r06
  ldw r05, r05, r1F
  or  r02, r05, r1F
  limm  r06, 0
  add r05, r03, r06
  ldw r09, r05, r1F
  add r08, r09, r08
  jr  r05, r02, r1F
min_caml_mul:
  limm  r0A, 31
  limm  r06, mul_sub.min_caml_mul23
  jr  r05, r06, r1F
