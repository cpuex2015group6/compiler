open Asm

let stackset = ref S.empty (* すでに Save された変数の集合 *)
let stackmap = ref [] (* Save された変数のスタックにおける位置 *)
let save x = 
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]
let locate x = 
  let rec loc = function 
    | [] -> []
    | y :: zs when x = y -> 0 :: List.map succ (loc zs)
    | y :: zs -> List.map succ (loc zs) in
    loc !stackmap
let offset x = try 1 * List.hd (locate x) with Failure("hd") -> prerr_endline ("variable '" ^ x ^ "' doesn't exist in stackmap");assert false
let stacksize () = align ((List.length !stackmap + 1) * 1)

let reg r = 
  if is_reg r 
  then String.sub r 1 (String.length r - 1)
  else r 

let print oc s =
  match oc with
  | None -> ()
  | Some oc -> Printf.fprintf oc "%s" s
    
let llabel oc r1 label =
  print oc (Printf.sprintf "\tlimm\t%s, %s\n" r1 label)

let op1 oc inst r1 imm =
  print oc (Printf.sprintf "\t%s\t%s, %d\n" inst r1 imm)

let op2i oc inst r1 r2 imm =
  print oc (Printf.sprintf "\t%s\t%s, %s, %d\n" inst r1 r2 imm)

let op2l oc inst r1 r2 label =
  print oc (Printf.sprintf "\t%s\t%s, %s, %s\n" inst r1 r2 label)

let op2ic oc inst r1 r2 imm condition =
  print oc (Printf.sprintf "\t%s\t%s, %s, %d, %d\n" inst r1 r2 imm condition)

let op2lc oc inst r1 r2 label condition =
  print oc (Printf.sprintf "\t%s\t%s, %s, %s, %d\n" inst r1 r2 label condition)

let op3 oc inst r1 r2 r3 =
  print oc (Printf.sprintf "\t%s\t%s, %s, %s\n" inst r1 r2 r3)

let op3c oc inst r1 r2 r3 condition =
  print oc (Printf.sprintf "\t%s\t%s, %s, %s, %d\n" inst r1 r2 r3 condition)

let op3ic oc inst r1 r2 imm r3 condition =
  print oc (Printf.sprintf "\t%s\t%s, %s, %d, %s, %d\n" inst r1 r2 imm r3 condition)

let op4 oc inst r1 r2 r3 r4 =
  print oc (Printf.sprintf "\t%s\t%s, %s, %s, %s\n" inst r1 r2 r3 r4)

let op4c oc inst r1 r2 r3 r4 condition =
  print oc (Printf.sprintf "\t%s\t%s, %s, %s, %s, %d\n" inst r1 r2 r3 r4 condition)

(* limmは内部でreg_tmpを破壊するので、 limm reg_tmp, 0 などとしてはいけない *)
let rec limm oc r1 imm =
  let limm_sub oc r1 imm =
    print oc (Printf.sprintf "\tlimm\t%s, %d\n" r1 imm) in
  match imm with
  | _ when imm >= 0 && imm < 32768 ->
     limm_sub oc r1 imm
  | _ when imm < 0 ->
     limm oc r1 (0x100000000 + imm)
  | _ ->
     let n = imm lsr 16 in
     let m = imm lxor (n lsl 16) in
     let r = r1 in
     limm_sub oc r n;
     limm_sub oc reg_tmp 16;
     op3 oc "sll" r r reg_tmp;
     limm_sub oc reg_tmp m;
     op3 oc "or" r r reg_tmp

(* 関数呼び出しのために引数を並べ替える (register shuffling) *)
let rec shuffle sw xys = 
  (* remove identical moves *)
  let (_, xys) = List.partition (fun (x, y) -> x = y) xys in
    (* find acyclic moves *)
    match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with
      | ([], []) -> []
      | ((x, y) :: xys, []) -> (* no acyclic moves; resolve a cyclic move *)
	  (y, sw) :: (x, y) :: 
	    shuffle sw (List.map (function 
				    | (y', z) when y = y' -> (sw, z)
				    | yz -> yz) xys)
      | (xys, acyc) -> acyc @ shuffle sw xys

let store_lr oc =
  save "reg_lr";
  let ix = (offset "reg_lr") in
  op2i oc "stwi" reg_sp reg_lr ix

let restore_lr oc =
  let ix = (offset "reg_lr") in
  op2i oc "ldwi" reg_lr reg_sp ix

let is_no_effect f g = function
  | Li _ | SetL _ | Mr _ | Tuple _ | Add _ | Sub _ | Xor _ | Or _ | And _ | Sll _ | Srl _ | Ldw _ | Cmp _ | Cmpa _ | In | GetHp | FAdd _ | FSub _ | FMul _ | FDiv _ | FCmp _ | FCmpa _ | FAbA _ | FAbs _ | Sqrt _ -> f ()
  | _ -> g ()
           
let rec look_while = function
  | Ans(exp) -> look_while' exp
  | Let(_, exp, e) -> if look_while' exp then true else look_while e
and look_while' = function
  | If(_, _, _, e1, e2) | FIf(_, _, _, e1, e2) -> look_while e1 || look_while e2
  | IfThen(_, e, _) | While(_, _, _, e) -> look_while e
  | CallCls _ | CallDir _ -> true
  | _ -> false
                                                         
    
let rec g oc cflag = function (* 命令列のアセンブリ生成 *)
  | (dest, Ans (exp)) -> g' oc cflag (dest, exp)
  | (dest, Let(xts, exp, e)) ->
     let cflag = g' oc cflag (NonTail (rm_t xts), exp) in
     g oc cflag (dest, e)
and g' oc cflag = function (* 各命令のアセンブリ生成 *)
  (* 末尾でなかったら計算結果を dest にセット *)
  | (NonTail(_), Nop) -> cflag
  | (NonTail([x]), Li(C(i))) -> 
     limm oc (reg x) i;
    cflag
  | (NonTail([x]), Li(L(Id.L(l)))) -> 
     op2l oc "ldwi" (reg x) (reg reg_zero) l;
    cflag
  | (NonTail([x]), SetL(Id.L(y))) -> 
     llabel oc (reg x) y;
    cflag
  | (NonTail([x]), Mr(y)) when x = y -> cflag
  | (NonTail([x]), Mr(y)) ->
     op3 oc "or" (reg x) (reg y) (reg reg_zero);
    cflag
  | (NonTail(xs), Tuple(ys)) ->
     assert (List.length xs = List.length ys);
    List.iter2 (fun x y -> if x <> y then op3 oc "or" (reg x) (reg y) (reg reg_zero)) xs ys;
    cflag
  | (NonTail([x]), Add(y, V(z))) -> 
     op3 oc "add" (reg x) (reg y) (reg z);
    cflag
  | (NonTail([x]), Add(y, C(z))) -> 
    op2i oc "addi" (reg x) (reg y) z;
    cflag
  | (NonTail([x]), Sub(y, V(z))) -> 
     op3 oc "sub" (reg x) (reg y) (reg z);
    cflag
  | (NonTail([x]), Sub(y, C(z))) -> 
    op2i oc "subi" (reg x) (reg y) z;
    cflag
  | (NonTail([x]), Xor(y, V(z))) -> 
     op3 oc "xor" (reg x) (reg y) (reg z);
    cflag
  | (NonTail([x]), Xor(y, C(z))) -> 
     limm oc reg_imm z;
    op3 oc "xor" (reg x) (reg y) reg_imm;
    cflag
  | (NonTail([x]), Or(y, V(z))) -> 
     op3 oc "or" (reg x) (reg y) (reg z);
    cflag
  | (NonTail([x]), Or(y, C(z))) -> 
     limm oc reg_imm z;
    op3 oc "or" (reg x) (reg y) reg_imm;
    cflag
  | (NonTail([x]), And(y, V(z))) -> 
     op3 oc "and" (reg x) (reg y) (reg z);
    cflag
  | (NonTail([x]), And(y, C(z))) -> 
     limm oc reg_imm z;
    op3 oc "and" (reg x) (reg y) reg_imm;
    cflag
  | (NonTail([x]), Sll(y, V(z))) -> 
     op3 oc "sll" (reg x) (reg y) (reg z);
    cflag
  | (NonTail([x]), Sll(y, C(z))) ->
     limm oc reg_imm z;
    op3 oc "sll" (reg x) (reg y) reg_imm;
    cflag
  | (NonTail([x]), Srl(y, V(z))) -> 
     op3 oc "srl" (reg x) (reg y) (reg z);
    cflag
  | (NonTail([x]), Srl(y, C(z))) ->
     limm oc reg_imm z;
    op3 oc "srl" (reg x) (reg y) reg_imm;
    cflag
  | (NonTail([x]), Ldw(y, V(z))) ->
    op3 oc "ldw" (reg x) (reg y) (reg z);
    cflag
  | (NonTail([x]), Ldw(y, C(z))) -> 
     op2i oc "ldwi" (reg x) (reg y) z;
     cflag
  | (NonTail(_), Stw(x, y, V(z))) ->
    op3 oc "stw" (reg y) (reg x) (reg z);
    cflag
  | (NonTail(_), Stw(x, y, C(z))) -> 
     op2i oc "stwi" (reg y) (reg x) z;
    cflag
  | (NonTail([x]), Cmp(c, y, V(z))) ->
     op3c oc "cmpc" (reg x) (reg y) (reg z) c;
     cflag
  | (NonTail([x]), Cmp(c, y, C(z))) ->
     op2ic oc "cmpic" (reg x) (reg y) z c;
     cflag
  | (NonTail([x]), FCmp(c, y, z)) ->
     op3c oc "fcmpc" (reg x) (reg y) (reg z) c;
     cflag
  | (NonTail([x]), Cmpa(c, y, V(z), w)) ->
     assert (x = w);
     op3c oc "cmpca" (reg x) (reg y) (reg z) c;
     cflag
  | (NonTail([x]), Cmpa(c, y, C(z), w)) ->
     assert (x = w);
     op2ic oc "cmpaic" (reg x) (reg y) z c;
     cflag
  | (NonTail([x]), FCmpa(c, y, z, w)) ->
     assert (x = w);
     op3c oc "fcmpac" (reg x) (reg y) (reg z) c;
     cflag
  | (NonTail([x]), FAdd(y, z)) -> 
     op3 oc "fadd" (reg x) (reg y) (reg z);
    cflag
  | (NonTail([x]), FSub(y, z)) -> 
     op3 oc "fsub" (reg x) (reg y) (reg z);
    cflag
  | (NonTail([x]), FMul(y, z)) -> 
     op3 oc "fmul" (reg x) (reg y) (reg z);
    cflag
  | (NonTail([x]), FDiv(y, z)) ->
     op3 oc "finv" reg_imm (reg z) (reg reg_zero);
    op3 oc "fmul" (reg x) (reg y) reg_imm;
    cflag
  | (NonTail([x]), FAbA(y, z)) -> 
     op3 oc "faba" (reg x) (reg y) (reg z);
    cflag
  | (NonTail([x]), FAbs(y)) -> 
     op3 oc "faba" (reg x) (reg y) (reg reg_zero);
    cflag
  | (NonTail([x]), Sqrt(y)) -> 
     op3 oc "fsqrt" (reg x) (reg y) (reg reg_zero);
    cflag
  | (NonTail([x]), In) -> 
     op1 oc "in" (reg x) 0;
    cflag
  | (NonTail([x]), Out(y)) -> 
     op1 oc "out" (reg y) 0;
    cflag
  | (NonTail([x]), GetHp) -> 
     op3 oc "or" (reg x) (reg reg_hp) (reg reg_zero);
    cflag
  | (NonTail([x]), SetHp(V(y))) ->
     op3 oc "or" (reg reg_hp) (reg y) (reg reg_zero);
    cflag
  | (NonTail([x]), SetHp(C(i))) ->
     limm oc (reg reg_hp) i;
    cflag
  | (NonTail(_), Comment(s)) ->
     print oc (Printf.sprintf "#\t%s\n" s);
    cflag
  (* 退避の仮想命令の実装 *)
  | (NonTail(_), Save(x, y)) when not (S.mem y !stackset) ->
     save y;
    op2i oc "stwi" reg_sp (reg x) (offset y);
    cflag
  | (NonTail(_), Save(x, y)) -> assert (S.mem y !stackset); cflag
  (* 復帰の仮想命令の実装 *)
  | (NonTail([x]), Restore(y)) ->
    op2i oc "ldwi" (reg x) reg_sp (offset y);
    cflag
  (* 末尾だったら計算結果を第一レジスタにセット *)
  | (Tail, (Nop | Stw _ | Out _ | Comment _ | Save _ as exp)) ->
     let cflag = g' oc cflag (NonTail([Id.gentmp Type.Unit]), exp) in
     (if cflag then restore_lr oc);
     op3 oc "jrf" reg_tmp (reg reg_zero) reg_lr;
     cflag
  | (Tail, (Restore(x) as exp)) ->
     let cflag = (match locate x with
       | [i] -> g' oc cflag (NonTail([regs.(0)]), exp)
       | [i; j] when (i + 1 = j) -> g' oc cflag (NonTail([regs.(0)]), exp)
       | _ -> assert false) in
     (if cflag then restore_lr oc);
     op3 oc "jrf" reg_tmp (reg reg_zero) reg_lr;
     cflag
  | (Tail, If(c, x, y, e1, e2)) ->
     g'_tail_if oc cflag c (reg x) (reg y) "" e1 e2
  | (Tail, FIf(c, x, y, e1, e2)) ->
     g'_tail_if oc cflag c (reg x) (reg y) "f" e1 e2
  | (Tail, IfThen(f, e, t)) ->
     g'_tail_ifthen oc cflag (reg f) e
  | (NonTail(z), If(c, x, y, e1, e2)) ->
     g'_non_tail_if oc cflag (NonTail(z)) c (reg x) (reg y) "" e1 e2
  | (NonTail(z), FIf(c, x, y, e1, e2)) ->
     g'_non_tail_if oc cflag (NonTail(z)) c (reg x) (reg y) "f" e1 e2
  | (NonTail(z), IfThen(f, e, t)) ->
     let tmp = List.rev z in
     let x = List.hd tmp in
     let tdest = List.rev (List.tl tmp) in
     List.iter2 (fun x dv -> assert (x = dv)) t tdest;
     g'_non_tail_ifthen oc cflag x (NonTail(z)) (reg f) e
  | (_ as t, While(Id.L(x), yts, zs, e)) ->
     List.iter2 (fun (y, _) z -> assert (y = z)) yts zs;
     let cflag =
       if not cflag then
         let cflag = look_while e in
         (if cflag then store_lr oc);
         cflag
       else cflag in
     print oc (Printf.sprintf "%s:\n" x);
     g oc cflag (t, e)
  | (_, Continue(Id.L(x), yts, zs, _, _)) ->
     op2l oc "jif" reg_tmp (reg reg_zero) x;
     cflag
  (* 関数呼び出しの仮想命令の実装 *)
  | (Tail, CallCls(x, ys)) -> (* 末尾呼び出し *)
     g'_args oc [(x, reg_cl)] ys;
    (if cflag then restore_lr oc);
    op3 oc "ldw" (reg reg_sw) (reg reg_cl) (reg reg_zero);
    op3 oc "jrf" reg_tmp (reg reg_zero) (reg reg_sw);
    true
  | (Tail, CallDir(Id.L(x), ys)) -> (* 末尾呼び出し *)
     g'_args oc [] ys;
    (if cflag then restore_lr oc);
    op2l oc "jif" reg_tmp (reg reg_zero) x;
    true
  | (NonTail([a]), CallCls(x, ys)) ->
     g'_args oc [(x, reg_cl)] ys;
    (if not cflag then store_lr oc);
    let ss = stacksize () in
    op2i oc "addi" reg_sp reg_sp ss;
    op3 oc "ldw"reg_tmp (reg reg_cl) (reg reg_zero);
    op3 oc "cr" reg_lr (reg reg_zero) reg_tmp;
    op2i oc "subi" reg_sp reg_sp ss;
    assert (a = regs.(0));
    true
  | (NonTail([a]), CallDir(Id.L(x), ys)) -> 
     g'_args oc [] ys;
    (if not cflag then store_lr oc);
    let ss = stacksize () in
    op2i oc "addi" reg_sp reg_sp ss;
    op2l oc "ci" reg_lr (reg reg_zero) x;
    op2i oc "subi" reg_sp reg_sp ss;
    assert (a = regs.(0));
    true
  | (NonTail _, _) -> assert false
  | (Tail, exp) ->
     is_no_effect (fun _ ->
       let cflag = g' oc cflag (NonTail([regs.(0)]), exp) in
       (if cflag then restore_lr oc);
       op3 oc "jrf" reg_tmp (reg reg_zero) reg_lr
     ) (fun _ -> assert false) exp;
    cflag
and g'_tail_if oc cflag c x y p e1 e2 =
  match e2 with
  | Ans(Nop) when not cflag ->
     op3c oc (p ^ "jrc") x y reg_lr (Asm.negcond c);
    g oc cflag (Tail, e1)
  | _ ->
     let b_else = Id.genid ("else") in
     op2lc oc (p ^ "jic") x y b_else (Asm.negcond c);
     let stackset_back = !stackset in
     let _ = g oc cflag (Tail, e1) in
     print oc (Printf.sprintf "%s:\n" b_else);
     stackset := stackset_back;
     g oc cflag (Tail, e2)
and g'_tail_ifthen oc cflag f e =
  op3 oc "jrf" (reg regs.(0)) f reg_lr;
  g oc cflag (Tail, e)
and g'_non_tail_if oc cflag dest c x y p e1 e2 =
  let b_cont = Id.genid ("cont") in
  let stackset' = !stackset in
  let stackmap' = !stackmap in
  let cflag1 = g None cflag (dest, e1) in
  let cflag2 = g None cflag (dest, e2) in
  stackset := stackset';
  stackmap := stackmap';
  let stackset_back = !stackset in
  if (cflag1 || cflag2) && (not cflag) then store_lr oc;
  let cflag = true in
  (match e2 with
  | Ans(Nop) ->
     op2lc oc (p ^ "jic") x y b_cont (Asm.negcond c);
     let _ = g oc cflag (dest, e1) in
     let stackset1 = !stackset in
     print oc (Printf.sprintf "%s:\n" b_cont);
     stackset := S.inter stackset1 stackset_back
  | _ ->
     let b_else = Id.genid ("else") in
     op2lc oc (p ^ "jic") x y b_else (Asm.negcond c);
     let _ = g oc cflag (dest, e1) in
     let stackset1 = !stackset in
     op2l oc "jif" reg_tmp (reg reg_zero) b_cont;
     print oc (Printf.sprintf "%s:\n" b_else);
     stackset := stackset_back;
     let _ = g oc cflag (dest, e2) in
     print oc (Printf.sprintf "%s:\n" b_cont);
     let stackset2 = !stackset in
     stackset := S.inter stackset1 stackset2);
  cflag1 || cflag2
and g'_non_tail_ifthen oc cflag destx dest f e =
  let b_cont = Id.genid ("cont") in
  let stackset' = !stackset in
  let stackmap' = !stackmap in
  let cflag1 = g None cflag (dest, e) in
  stackset := stackset';
  stackmap := stackmap';
  let stackset_back = !stackset in
  if cflag1 && (not cflag) then store_lr oc;
  let cflag = true in
  op2l oc "jif" (reg destx) f b_cont;
  let _ = g oc cflag (dest, e) in
  let stackset1 = !stackset in
  print oc (Printf.sprintf "%s:\n" b_cont);
  stackset := S.inter stackset1 stackset_back;
  cflag1
and g'_args oc x_reg_cl ys = 
(*  let (i, yrs) = 
    List.fold_left
      (fun (i, yrs) y -> (i + 1, (y, regs.(i)) :: yrs))
      (0, x_reg_cl) ys in
  List.iter
    (fun (y, r) -> op3 oc "or" (reg r) (reg y) (reg reg_zero))
    (shuffle reg_sw yrs)*)
  ()

let h oc { name = Id.L(x); args = _; body = e; ret = _ } =
  Printf.fprintf oc "%s:\n" x;
  stackset := S.empty;
  stackmap := [];
  let _ = g (Some oc) false (Tail, e) in
  ()
       
let f oc (Prog(data, vars, fundefs, e)) =
  show fundefs e;
  print_endline "";
  Format.eprintf "generating assembly...@.";
  Printf.fprintf oc "\t.text\n";
  Printf.fprintf oc "\t.globl  _min_caml_init\n";
  Printf.fprintf oc "\t.align 2\n";
  op2l (Some oc) "jif" reg_tmp (reg reg_zero) "_min_caml_init";
  (if data <> [] then
      (Printf.fprintf oc "\t.data\n\t.literal8\n";
       List.iter
	 (fun (Id.L(x), d) ->
	   Printf.fprintf oc "\t.align 3\n";
	   Printf.fprintf oc "%s:\n" x;
	   Printf.fprintf oc "\t.long\t%d\n" d)
	 data));
  Printf.fprintf oc "\t.text\n";
  Printf.fprintf oc "\t.align 2\n";
  List.iter (fun fundef -> h oc fundef) fundefs;
  Printf.fprintf oc "_min_caml_init: # main entry point\n";
  Printf.fprintf oc "   # stack start from 2MB\n";
  limm (Some oc) reg_sp stack_start;
  Printf.fprintf oc "   # heap start from 1024B\n";
  limm (Some oc) (reg reg_hp) heap_start;
  Printf.fprintf oc "   # main program start\n";
  Printf.fprintf oc "_min_caml_start: # main entry point\n";
  limm (Some oc) (reg reg_m1) 0xFFFFFFFF;
  stackset := S.empty;
  stackmap := [];
  let _ = g (Some oc) false (NonTail([regs.(0)]), e) in
  op1 (Some oc) "hlt" (reg reg_zero) 0;
  Printf.fprintf oc "   # main program end\n";
