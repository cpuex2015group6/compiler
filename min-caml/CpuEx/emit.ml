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
let offset x = prerr_endline x;1 * List.hd (locate x)
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

let op3 oc inst r1 r2 r3 =
  print oc (Printf.sprintf "\t%s\t%s, %s, %s\n" inst r1 r2 r3)

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
	 
type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 *)
let rec g oc cflag = function (* 命令列のアセンブリ生成 *)
  | (dest, Ans (exp)) -> g' oc cflag (dest, exp)
  | (dest, Let((x, t), exp, e)) ->
     let cflag = g' oc cflag (NonTail (x), exp) in
     g oc cflag (dest, e)
and g' oc cflag = function (* 各命令のアセンブリ生成 *)
  (* 末尾でなかったら計算結果を dest にセット *)
  | (NonTail(_), Nop) -> cflag
  | (NonTail(x), Li(C(i))) -> 
     limm oc (reg x) i;
    cflag
  | (NonTail(x), Li(L(Id.L(l)))) -> 
     op2l oc "ldwi" (reg x) (reg reg_zero) l;
    cflag
  | (NonTail(x), FLi(C(i))) -> 
     limm oc (reg x) i;
    cflag
  | (NonTail(x), FLi(L(Id.L(l)))) ->
    op2l oc "ldwi" (reg x) (reg reg_zero) l;
    cflag
  | (NonTail(x), SetL(Id.L(y))) -> 
     llabel oc (reg x) y;
    cflag
  | (NonTail(x), Mr(y)) when x = y -> cflag
  | (NonTail(x), Mr(y)) ->
     op3 oc "or" (reg x) (reg y) (reg reg_zero);
    cflag
  | (NonTail(x), Add(y, V(z))) -> 
     op3 oc "add" (reg x) (reg y) (reg z);
    cflag
  | (NonTail(x), Add(y, C(z))) -> 
    op2i oc "addi" (reg x) (reg y) z;
    cflag
  | (NonTail(x), Sub(y, V(z))) -> 
     op3 oc "sub" (reg x) (reg y) (reg z);
    cflag
  | (NonTail(x), Sub(y, C(z))) -> 
    op2i oc "subi" (reg x) (reg y) z;
    cflag
  | (NonTail(x), Xor(y, V(z))) -> 
     op3 oc "xor" (reg x) (reg y) (reg z);
    cflag
  | (NonTail(x), Xor(y, C(z))) -> 
     limm oc reg_imm z;
    op3 oc "xor" (reg x) (reg y) reg_imm;
    cflag
  | (NonTail(x), Or(y, V(z))) -> 
     op3 oc "or" (reg x) (reg y) (reg z);
    cflag
  | (NonTail(x), Or(y, C(z))) -> 
     limm oc reg_imm z;
    op3 oc "or" (reg x) (reg y) reg_imm;
    cflag
  | (NonTail(x), And(y, V(z))) -> 
     op3 oc "and" (reg x) (reg y) (reg z);
    cflag
  | (NonTail(x), And(y, C(z))) -> 
     limm oc reg_imm z;
    op3 oc "and" (reg x) (reg y) reg_imm;
    cflag
  | (NonTail(x), Sll(y, V(z))) -> 
     op3 oc "sll" (reg x) (reg y) (reg z);
    cflag
  | (NonTail(x), Sll(y, C(z))) -> 
     limm oc reg_imm z;
    op3 oc "sll" (reg x) (reg y) reg_imm;
    cflag
  | (NonTail(x), Srl(y, V(z))) -> 
     op3 oc "srl" (reg x) (reg y) (reg z);
    cflag
  | (NonTail(x), Srl(y, C(z))) -> 
     limm oc reg_imm z;
    op3 oc "srl" (reg x) (reg y) reg_imm;
    cflag
  | (NonTail(x), Ldw(y, V(z))) ->
    op3 oc "ldw" (reg x) (reg y) (reg z);
    cflag
  | (NonTail(x), Ldw(y, C(z))) -> 
     op2i oc "ldwi" (reg x) (reg y) z;
     cflag
  | (NonTail(_), Stw(x, y, V(z))) ->
    op3 oc "stw" (reg y) (reg x) (reg z);
    cflag
  | (NonTail(_), Stw(x, y, C(z))) -> 
     op2i oc "stwi" (reg y) (reg x) z;
     cflag
  | (NonTail(x), FMr(y)) when x = y -> cflag
  | (NonTail(x), FMr(y)) ->
     op3 oc "or" (reg x) (reg y) (reg reg_zero);
    cflag
  | (NonTail(x), FAdd(y, z)) -> 
     op3 oc "fadd" (reg x) (reg y) (reg z);
    cflag
  | (NonTail(x), FMul(y, z)) -> 
     op3 oc "fmul" (reg x) (reg y) (reg z);
    cflag
  | (NonTail(x), FDiv(y, z)) ->
     op3 oc "finv" reg_imm (reg z) (reg reg_zero);
    op3 oc "fmul" (reg x) (reg y) reg_imm;
    cflag
  | (NonTail(x), FAbs(y)) -> 
     op3 oc "fabs" (reg x) (reg y) (reg reg_zero);
    cflag
  | (NonTail(x), Sqrt(y)) -> 
     op3 oc "fsqrt" (reg x) (reg y) (reg reg_zero);
    cflag
  | (NonTail(x), Lfd(y, V(z))) ->
    op3 oc "ldw" (reg x) (reg y) (reg z);
    cflag
  | (NonTail(x), Lfd(y, C(z))) -> 
     op2i oc "ldwi" (reg x) (reg y) z;
     cflag
  | (NonTail(_), Stfd(x, y, V(z))) ->
    op3 oc "stw" (reg y) (reg x) (reg z);
    cflag
  | (NonTail(_), Stfd(x, y, C(z))) -> 
     op2i oc "stwi" (reg y) (reg x) z;
     cflag
  | (NonTail(x), ToFloat(y)) when x = y -> cflag
  | (NonTail(x), ToFloat(y)) -> 
     op3 oc "or" (reg x) (reg y) (reg reg_zero);
    cflag
  | (NonTail(x), ToInt(y)) when x = y -> cflag
  | (NonTail(x), ToInt(y)) -> 
     op3 oc "or" (reg x) (reg y) (reg reg_zero);
    cflag
  | (NonTail(x), ToArray(y)) when x = y -> cflag
  | (NonTail(x), ToArray(y)) -> 
     op3 oc "or" (reg x) (reg y) (reg reg_zero);
    cflag
  | (NonTail(x), In) -> 
     op1 oc "in" (reg x) 0;
    cflag
  | (NonTail(x), Out(y)) -> 
     op1 oc "out" (reg y) 0;
    cflag
  | (NonTail(x), Count) -> 
     op1 oc "count" (reg reg_zero) 0;
    cflag
  | (NonTail(x), ShowExec) ->
     op1 oc "showexec" (reg reg_zero) 0;
    cflag
  | (NonTail(x), SetCurExec) ->
     op1 oc "setcurexec" (reg reg_zero) 0;
    cflag
  | (NonTail(x), GetExecDiff) ->
     op1 oc "getexecdiff" (reg reg_zero) 0;
    cflag
  | (NonTail(x), GetHp) -> 
     op3 oc "or" (reg x) (reg reg_hp) (reg reg_zero);
    cflag
  | (NonTail(x), SetHp(y)) ->
     op3 oc "or" (reg reg_hp) (reg y) (reg reg_zero);
    cflag
  | (NonTail(_), Comment(s)) ->
     print oc (Printf.sprintf "#\t%s\n" s);
    cflag
  (* 退避の仮想命令の実装 *)
  | (NonTail(_), Save(x, y)) when not (S.mem y !stackset) ->
     save y;
    (*print oc (Printf.sprintf "save %s,%d\n" y (offset y));*)
    op2i oc "stwi" reg_sp (reg x) (offset y);
    cflag
  | (NonTail(_), Save(x, y)) -> assert (S.mem y !stackset); cflag
  (* 復帰の仮想命令の実装 *)
  | (NonTail(x), Restore(y)) ->
    (*print oc (Printf.sprintf "restore %s,%d\n" y (offset y));*)
    op2i oc "ldwi" (reg x) reg_sp (offset y);
    cflag
  (* 末尾だったら計算結果を第一レジスタにセット *)
  | (Tail, (Nop | Stw _ | Stfd _ | Out _ | Comment _ | Save _ as exp)) ->
     let cflag = g' oc cflag (NonTail(Id.gentmp Type.Unit), exp) in
     (if cflag then restore_lr oc);
     op3 oc "jr" reg_tmp reg_lr (reg reg_zero);
     cflag
  | (Tail, (Li _ | SetL _ | Mr _ | Add _ | Sub _ | Xor _ | Or _ | And _ | Sll _ | Srl _ | Ldw _ | In | Count | ShowExec | SetCurExec | GetExecDiff | GetHp | SetHp _ | ToInt _ | ToArray _ | FLi _ | FMr _ | FAdd _ | FMul _ | FDiv _ | FAbs _ | Sqrt _ | ToFloat _ | Lfd _ as exp)) ->
     let cflag = g' oc cflag (NonTail(regs.(0)), exp) in
     (if cflag then restore_lr oc);
     op3 oc "jr" reg_tmp reg_lr (reg reg_zero);
     cflag
  | (Tail, (Restore(x) as exp)) ->
     let cflag = (match locate x with
       | [i] -> g' oc cflag (NonTail(regs.(0)), exp)
       | [i; j] when (i + 1 = j) -> g' oc cflag (NonTail(regs.(0)), exp)
       | _ -> assert false) in
     (if cflag then restore_lr oc);
     op3 oc "jr" reg_tmp reg_lr (reg reg_zero);
     cflag
  | (Tail, IfEq(x, V(y), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg y);
     g'_tail_if oc cflag e1 e2 "jreqi" "jrneqi"
  | (Tail, IfEq(x, C(0), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg reg_zero);
     g'_tail_if oc cflag e1 e2 "jreqi" "jrneqi"
  | (Tail, IfEq(x, C(y), e1, e2)) ->
     op2i oc "cmpi" reg_cond (reg x) y;
     g'_tail_if oc cflag e1 e2 "jreqi" "jrneqi"
  | (Tail, IfLE(x, V(y), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg y);
     g'_tail_if oc cflag e1 e2 "jrlei" "jrgti"
  | (Tail, IfLE(x, C(0), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg reg_zero);
     g'_tail_if oc cflag e1 e2 "jrlei" "jrgti"
  | (Tail, IfLE(x, C(y), e1, e2)) ->
     op2i oc "cmpi" reg_cond (reg x) y;
     g'_tail_if oc cflag e1 e2 "jrlei" "jrgti"
  | (Tail, IfGE(x, V(y), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg y);
     g'_tail_if oc cflag e1 e2 "jrgei" "jrlti"
  | (Tail, IfGE(x, C(0), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg reg_zero);
     g'_tail_if oc cflag e1 e2 "jrgei" "jrlti"
  | (Tail, IfGE(x, C(y), e1, e2)) ->
     op2i oc "cmpi" reg_cond (reg x) y;
     g'_tail_if oc cflag e1 e2 "jrgei" "jrlti"
  | (Tail, IfFEq(x, y, e1, e2)) ->
     op3 oc "fcmp" reg_cond (reg x) (reg y);
     g'_tail_if oc cflag e1 e2 "jreqi" "jrneqi"
  | (Tail, IfFLE(x, y, e1, e2)) ->
     op3 oc "fcmp" reg_cond (reg x) (reg y);
     g'_tail_if oc cflag e1 e2 "jrlei" "jrgti"
  | (NonTail(z), IfEq(x, V(y), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg y);
     g'_non_tail_if oc cflag (NonTail(z)) e1 e2 "jreqi" "jrneqi"
  | (NonTail(z), IfEq(x, C(0), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg reg_zero);
     g'_non_tail_if oc cflag (NonTail(z)) e1 e2 "jreqi" "jrneqi"
  | (NonTail(z), IfEq(x, C(y), e1, e2)) ->
     op2i oc "cmpi" reg_cond (reg x) y;
     g'_non_tail_if oc cflag (NonTail(z)) e1 e2 "jreqi" "jrneqi"
  | (NonTail(z), IfLE(x, V(y), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg y);
     g'_non_tail_if oc cflag (NonTail(z)) e1 e2 "jrlei" "jrgti"
  | (NonTail(z), IfLE(x, C(0), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg reg_zero);
     g'_non_tail_if oc cflag (NonTail(z)) e1 e2 "jrlei" "jrgti"
  | (NonTail(z), IfLE(x, C(y), e1, e2)) ->
     op2i oc "cmpi" reg_cond (reg x) y;
     g'_non_tail_if oc cflag (NonTail(z)) e1 e2 "jrlei" "jrgti"
  | (NonTail(z), IfGE(x, V(y), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg y);
     g'_non_tail_if oc cflag (NonTail(z)) e1 e2 "jrgei" "jrlti"
  | (NonTail(z), IfGE(x, C(0), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg reg_zero);
     g'_non_tail_if oc cflag (NonTail(z)) e1 e2 "jrgei" "jrlti"
  | (NonTail(z), IfGE(x, C(y), e1, e2)) ->
     op2i oc "cmpi" reg_cond (reg x) y;
     g'_non_tail_if oc cflag (NonTail(z)) e1 e2 "jrgei" "jrlti"
  | (NonTail(z), IfFEq(x, y, e1, e2)) ->
     op3 oc "fcmp" reg_cond (reg x) (reg y);
     g'_non_tail_if oc cflag (NonTail(z)) e1 e2 "jreqi" "jrneqi"
  | (NonTail(z), IfFLE(x, y, e1, e2)) ->
     op3 oc "fcmp" reg_cond (reg x) (reg y);
     g'_non_tail_if oc cflag (NonTail(z)) e1 e2 "jrlei" "jrgti"
  (* 関数呼び出しの仮想命令の実装 *)
  | (Tail, CallCls(x, ys)) -> (* 末尾呼び出し *)
     g'_args oc [(x, reg_cl)] ys;
    (if cflag then restore_lr oc);
    op3 oc "ldw" (reg reg_sw) (reg reg_cl) (reg reg_zero);
    op3 oc "jr" reg_tmp (reg reg_sw) (reg reg_zero);
    true
  | (Tail, CallDir(Id.L(x), ys)) -> (* 末尾呼び出し *)
     g'_args oc [] ys;
    (if cflag then restore_lr oc);
    op2l oc "jri" reg_tmp (reg reg_zero) x;
    true
  | (NonTail(a), CallCls(x, ys)) ->
     g'_args oc [(x, reg_cl)] ys;
    (if not cflag then store_lr oc);
    let ss = stacksize () in
    op2i oc "addi" reg_sp reg_sp ss;
    op3 oc "ldw"reg_tmp (reg reg_cl) (reg reg_zero);
    op3 oc "jr" reg_lr reg_tmp (reg reg_zero);
    op2i oc "subi" reg_sp reg_sp ss;
    (if List.mem a allregs && a <> regs.(0) then 
        op3 oc "or" (reg a) (reg regs.(0)) (reg reg_zero));
    true
  | (NonTail(a), CallDir(Id.L(x), ys)) -> 
     g'_args oc [] ys;
    (if not cflag then store_lr oc);
    let ss = stacksize () in
    op2i oc "addi" reg_sp reg_sp ss;
    op2l oc "jri" reg_lr (reg reg_zero) x;
    op2i oc "subi" reg_sp reg_sp ss;
    (if List.mem a allregs && a <> regs.(0) then
	op3 oc "or" (reg a) (reg regs.(0)) (reg reg_zero));
    true
and g'_tail_if oc cflag e1 e2 b bn = 
  let b_else = Id.genid (b ^ "_else") in
  op2l oc bn reg_tmp reg_cond b_else;
  let stackset_back = !stackset in
  let _ = g oc cflag (Tail, e1) in
  print oc (Printf.sprintf "%s:\n" b_else);
  stackset := stackset_back;
  g oc cflag (Tail, e2)
and g'_non_tail_if oc cflag dest e1 e2 b bn = 
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
  let stackset' = !stackset in
  let stackmap' = !stackmap in
  let cflag1 = g None cflag (dest, e1) in
  let cflag2 = g None cflag (dest, e2) in
  stackset := stackset';
  stackmap := stackmap';
  op3 oc bn reg_tmp reg_cond b_else;
  let stackset_back = !stackset in
  let _ = g oc cflag (dest, e1) in
  let stackset1 = !stackset in
  (if (cflag1 || cflag2) && (not cflag) && (not cflag1) then store_lr oc);
  op2l oc "jri" reg_tmp (reg reg_zero) b_cont;
  print oc (Printf.sprintf "%s:\n" b_else);
  stackset := stackset_back;
  let _ = g oc cflag (dest, e2) in
  (if (cflag1 || cflag2) && (not cflag) && (not cflag2) then store_lr oc);
  print oc (Printf.sprintf "%s:\n" b_cont);
  let stackset2 = !stackset in
  stackset := S.inter stackset1 stackset2;
  cflag1 || cflag2
and g'_args oc x_reg_cl ys = 
  let (i, yrs) = 
    List.fold_left
      (fun (i, yrs) y -> (i + 1, (y, regs.(i)) :: yrs))
      (0, x_reg_cl) ys in
  List.iter
    (fun (y, r) -> op3 oc "or" (reg r) (reg y) (reg reg_zero))
    (shuffle reg_sw yrs)

let h oc { name = Id.L(x); args = _; body = e; ret = _ } =
  Printf.fprintf oc "%s:\n" x;
  stackset := S.empty;
  stackmap := [];
  let _ = g (Some oc) false (Tail, e) in
  ()

(* デバッグ用 *)
let rec i indent = function
  | (dest, Ans (exp)) -> i' indent (dest, exp)
  | (dest, Let((x, t), exp, e)) -> i' indent (NonTail (x), exp); i indent (dest, e)
and i' indent = function
  | (NonTail(x), exp) ->
     print_string (indent^x^" ");
     j indent exp
  | (Tail, exp) ->
     print_string (indent^"_ ");
     j indent exp
and j indent = function
  | Nop ->
     Printf.fprintf stdout "nop\n"
  | Li(C(i)) ->
     Printf.fprintf stdout "li %d\n" i
  | Li(L(Id.L(l))) ->
     Printf.fprintf stdout "li %s\n" l
  | FLi(C(i)) ->
     Printf.fprintf stdout "fli %d\n" i
  | FLi(L(Id.L(l))) ->
     Printf.fprintf stdout "fli %s\n" l
  | SetL(Id.L(y)) -> 
     Printf.fprintf stdout "setl %s\n" y
  | Mr(y) ->
     Printf.fprintf stdout "mr %s\n" y
  | Add(y, V(z)) -> 
     Printf.fprintf stdout "add %s, %s\n" y z
  | Add(y, C(z)) -> 
     Printf.fprintf stdout "add %s, %d\n" y z
  | Sub(y, V(z)) -> 
     Printf.fprintf stdout "sub %s, %s\n" y z
  | Sub(y, C(z)) -> 
     Printf.fprintf stdout "sub %s, %d\n" y z
  | Xor(y, V(z)) -> 
     Printf.fprintf stdout "xor %s, %s\n" y z
  | Xor(y, C(z)) -> 
     Printf.fprintf stdout "xor %s, %d\n" y z
  | Or(y, V(z)) -> 
     Printf.fprintf stdout "or %s, %s\n" y z
  | Or(y, C(z)) -> 
     Printf.fprintf stdout "or %s, %d\n" y z
  | And(y, V(z)) -> 
     Printf.fprintf stdout "and %s, %s\n" y z
  | And(y, C(z)) -> 
     Printf.fprintf stdout "and %s, %d\n" y z
  | Sll(y, V(z)) -> 
     Printf.fprintf stdout "sll %s, %s\n" y z
  | Sll(y, C(z)) -> 
     Printf.fprintf stdout "sll %s, %d\n" y z
  | Srl(y, V(z)) -> 
     Printf.fprintf stdout "srl %s, %s\n" y z
  | Srl(y, C(z)) -> 
     Printf.fprintf stdout "srl %s, %d\n" y z
  | Ldw(y, V(z)) ->
     Printf.fprintf stdout "ldw %s, %s\n" y z
  | Ldw(y, C(z)) -> 
     Printf.fprintf stdout "ldw %s, %d\n" y z
  | Stw(x, y, V(z)) ->
     Printf.fprintf stdout "stw %s, %s, %s\n" x y z
  | Stw(x, y, C(z)) -> 
     Printf.fprintf stdout "stw %s, %s, %d\n" x y z
  | FMr(y) ->
     Printf.fprintf stdout "fmr %s\n" y
  | FAdd(y, z) -> 
     Printf.fprintf stdout "fadd %s, %s\n" y z
  | FMul(y, z) -> 
     Printf.fprintf stdout "fmul %s, %s\n" y z
  | FDiv(y, z) -> 
     Printf.fprintf stdout "fdiv %s, %s\n" y z
  | FAbs(y) -> 
     Printf.fprintf stdout "fabs %s\n" y
  | Sqrt(y) -> 
     Printf.fprintf stdout "sqrt %s\n" y
  | Lfd(y, V(z)) ->
     Printf.fprintf stdout "lfd %s, %s\n" y z
  | Lfd(y, C(z)) -> 
     Printf.fprintf stdout "lfd %s, %d\n" y z
  | Stfd(x, y, V(z)) ->
     Printf.fprintf stdout "stfd %s, %s, %s\n" x y z
  | Stfd(x, y, C(z)) -> 
     Printf.fprintf stdout "stfd %s, %s, %d\n" x y z
  | ToFloat(y) -> 
     Printf.fprintf stdout "tofloat %s\n" y
  | ToInt(y) -> 
     Printf.fprintf stdout "toint %s\n" y
  | ToArray(y) -> 
     Printf.fprintf stdout "toarray %s\n" y
  | In -> 
     Printf.fprintf stdout "in\n"
  | Out(y) -> 
     Printf.fprintf stdout "out %s\n" y
  | Count -> 
     Printf.fprintf stdout "count\n"
  | ShowExec -> 
     Printf.fprintf stdout "showexec\n"
  | SetCurExec ->
     Printf.fprintf stdout "setcurexec\n"
  | GetExecDiff ->
     Printf.fprintf stdout "getexecdiff\n"
  | GetHp -> 
     Printf.fprintf stdout "gethp\n"
  | SetHp(y) -> 
     Printf.fprintf stdout "sethp %s\n" y
  | Comment(s) ->
     Printf.fprintf stdout "comment %s\n" s
  | Save(x, y) ->
     Printf.fprintf stdout "save %s,%s\n" y x
  | Restore(y) ->
     Printf.fprintf stdout "restore %s\n" y
  | IfEq(x, V(y), e1, e2) ->
     Printf.fprintf stdout "ifeq %s, %s\n" x y;
     let indent = indent ^ "  "
     in
     Printf.fprintf stdout "%scont:\n" indent;
     print_string indent;
     i indent (Tail, e1);
     Printf.fprintf stdout "%selse:\n" indent;
     print_string indent;
     i indent (Tail, e2)
  | IfEq(x, C(y), e1, e2) ->
     Printf.fprintf stdout "ifeq %s, %d\n" x y;
     let indent = indent ^ "  "
     in
     Printf.fprintf stdout "%scont:\n" indent;
     print_string indent;
     i indent (Tail, e1);
     Printf.fprintf stdout "%selse:\n" indent;
     print_string indent;
     i indent (Tail, e2)
  | IfLE(x, V(y), e1, e2) ->
     Printf.fprintf stdout "ifle %s, %s\n" x y;
     let indent = indent ^ "  "
     in
     Printf.fprintf stdout "%scont:\n" indent;
     print_string indent;
     i indent (Tail, e1);
     Printf.fprintf stdout "%selse:\n" indent;
     print_string indent;
     i indent (Tail, e2)
  | IfLE(x, C(y), e1, e2) ->
     Printf.fprintf stdout "ifle %s, %d\n" x y;
     let indent = indent ^ "  "
     in
     Printf.fprintf stdout "%scont:\n" indent;
     print_string indent;
     i indent (Tail, e1);
     Printf.fprintf stdout "%selse:\n" indent;
     print_string indent;
     i indent (Tail, e2)
  | IfGE(x, V(y), e1, e2) ->
     Printf.fprintf stdout "ifge %s, %s\n" x y;
     let indent = indent ^ "  "
     in
     Printf.fprintf stdout "%scont:\n" indent;
     print_string indent;
     i indent (Tail, e1);
     Printf.fprintf stdout "%selse:\n" indent;
     print_string indent;
     i indent (Tail, e2)
  | IfGE(x, C(y), e1, e2) ->
     Printf.fprintf stdout "ifge %s, %d\n" x y;
     let indent = indent ^ "  "
     in
     Printf.fprintf stdout "%scont:\n" indent;
     print_string indent;
     i indent (Tail, e1);
     Printf.fprintf stdout "%selse:\n" indent;
     print_string indent;
     i indent (Tail, e2)
  | IfFEq(x, y, e1, e2) ->
     Printf.fprintf stdout "iffeq %s, %s\n" x y;
     let indent = indent ^ "  "
     in
     Printf.fprintf stdout "%scont:\n" indent;
     print_string indent;
     i indent (Tail, e1);
     Printf.fprintf stdout "%selse:\n" indent;
     print_string indent;
     i indent (Tail, e2)
  | IfFLE(x, y, e1, e2) ->
     Printf.fprintf stdout "iffle %s, %s\n" x y;
     let indent = indent ^ "  "
     in
     Printf.fprintf stdout "%scont:\n" indent;
     print_string indent;
     i indent (Tail, e1);
     Printf.fprintf stdout "%selse:\n" indent;
     print_string indent;
     i indent (Tail, e2)
  | CallCls(x, ys) ->
     Printf.fprintf stdout "callcls %s, " x;
     Printf.fprintf stdout "ys:";
     List.iter (fun y -> Printf.fprintf stdout "%s, " y) ys;
     Printf.fprintf stdout "\n"
  | CallDir(Id.L(x), ys) -> 
     Printf.fprintf stdout "calldir %s, " x;
     Printf.fprintf stdout "ys:";
     List.iter (fun y -> Printf.fprintf stdout "%s, " y) ys;
     Printf.fprintf stdout "\n"

let show fundefs e =
  print_endline ">>>>>>>>>>>>>>>>emit.ml>>>>>>>>>>>>>>>>>";
  List.iter (fun {name= Id.L(name); args=_; body= e; ret=r} -> print_string (name^":\n"); i "" (Tail, e)) fundefs;
  print_endline "min_caml_start:";
  i "" (NonTail("r08"), e)
       
let f oc (Prog(data, vars, fundefs, e)) =
  show fundefs e;
  Format.eprintf "generating assembly...@.";
  Printf.fprintf oc "\t.text\n";
  Printf.fprintf oc "\t.globl  _min_caml_init\n";
  Printf.fprintf oc "\t.align 2\n";
  op2l (Some oc) "jri" reg_tmp (reg reg_zero) "_min_caml_init";
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
  stackset := S.empty;
  stackmap := [];
  let _ = g (Some oc) false (NonTail("r08"), e) in
  op1 (Some oc) "hlt" (reg reg_zero) 0;
  Printf.fprintf oc "   # main program end\n";
