# print_newline
	.text
	.align	2
	.globl 	min_caml_print_newline
min_caml_print_newline: 
  limm r08, 10
  out r08, 0
  jr  r05, r02, rFF
#	print_int
	.text
	.align 	2
	.globl	min_caml_print_int
min_caml_print_int: 
  limm r05, 8
  limm r06, 48
  add r09, r08, r06
  out r09, 0
  srl r08, r08, r05
  add r09, r08, r06
  out r09, 0
  srl r08, r08, r05
  add r09, r08, r06
  out r09, 0
  srl r08, r08, r05
  add r09, r08, r06
  out r09, 0
  jr  r05, r02, rFF
#	print_byte
	.text
	.align 	2
  .globl	min_caml_print_byte
min_caml_print_byte:  
  out r08, 0
  jr  r05, r02, rFF
#	prerr_int
	.text
	.align 	2
	.globl 	min_caml_prerr_int
min_caml_prerr_int: 
  limm r05, 8
  limm r06, 48
  add r09, r08, r06
  out r09, 0
  srl r08, r08, r05
  add r09, r08, r06
  out r09, 0
  srl r08, r08, r05
  add r09, r08, r06
  out r09, 0
  srl r08, r08, r05
  add r09, r08, r06
  out r09, 0
  jr  r05, r02, rFF
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
#min_caml_prerr_float:
#	read_int
	.text
	.align 	2
#	.globl	min_caml_read_int
# 	read_float
	.text
	.align	2
#	.globl	min_caml_read_float
#	create_array
	.text
	.align	2
#	.globl	min_caml_create_array
#	create_float_array
	.text
	.align	2
#	.globl	min_caml_create_float_array
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
# int_of_float
#let rec int_of_float i =
#    let exp = ((i lsr 23) land 255) - 127 in
#    let rval = (((i lor 8388608) land 16777215) lsr (23 - exp)) in
#    rval lor (i land 2147483648)
#      in
#      print_int (int_of_float 1091567616)
	.text
	.align	2
	.globl	min_caml_int_of_float
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
# truncate
	.text
	.align	2
#	.globl	min_caml_truncate
  
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
  
