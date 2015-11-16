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
let offset x = 1 * List.hd (locate x)
let stacksize () = align ((List.length !stackmap + 1) * 1)

let reg r = 
  if is_reg r 
  then String.sub r 1 (String.length r - 1)
  else r 

let llabel oc r1 label =
  Printf.fprintf oc "\tlimm\t%s, %s\n" r1 label

let op1 oc inst r1 imm =
  Printf.fprintf oc "\t%s\t%s, %d\n" inst r1 imm

let op3 oc inst r1 r2 r3 =
  Printf.fprintf oc "\t%s\t%s, %s, %s\n" inst r1 r2 r3

(* limmは内部でreg_tmpを破壊するので、 limm reg_tmp, 0 などとしてはいけない *)
let rec limm oc r1 imm =
  let limm_sub oc r1 imm =
    Printf.fprintf oc "\tlimm\t%s, %d\n" r1 imm in
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

type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 *)
let rec g oc = function (* 命令列のアセンブリ生成 *)
  | (dest, Ans (exp)) -> g' oc (dest, exp)
  | (dest, Let((x, t), exp, e)) -> g' oc (NonTail (x), exp); g oc (dest, e)
and g' oc = function (* 各命令のアセンブリ生成 *)
  (* 末尾でなかったら計算結果を dest にセット *)
  | (NonTail(_), Nop) -> ()
  | (NonTail(x), Li(i)) -> 
     limm oc (reg x) i
  | (NonTail(x), FLi(Id.L(l))) ->
     llabel oc reg_imm l;
     op3 oc "ldw" (reg x) reg_imm reg_zero
  | (NonTail(x), SetL(Id.L(y))) -> 
     llabel oc (reg x) y
  | (NonTail(x), Mr(y)) when x = y -> ()
  | (NonTail(x), Mr(y)) ->
     op3 oc "or" (reg x) (reg y) reg_zero
  | (NonTail(x), Add(y, V(z))) -> 
     op3 oc "add" (reg x) (reg y) (reg z)
  | (NonTail(x), Add(y, C(z))) -> 
     limm oc reg_imm z;
     op3 oc "add" (reg x) (reg y) reg_imm
  | (NonTail(x), Sub(y, V(z))) -> 
     op3 oc "sub" (reg x) (reg y) (reg z)
  | (NonTail(x), Sub(y, C(z))) -> 
     limm oc reg_imm z;
     op3 oc "sub" (reg x) (reg y) reg_imm
  | (NonTail(x), Xor(y, V(z))) -> 
     op3 oc "xor" (reg x) (reg y) (reg z)
  | (NonTail(x), Xor(y, C(z))) -> 
     limm oc reg_imm z;
     op3 oc "xor" (reg x) (reg y) reg_imm
  | (NonTail(x), Or(y, V(z))) -> 
     op3 oc "or" (reg x) (reg y) (reg z)
  | (NonTail(x), Or(y, C(z))) -> 
     limm oc reg_imm z;
     op3 oc "or" (reg x) (reg y) reg_imm
  | (NonTail(x), And(y, V(z))) -> 
     op3 oc "and" (reg x) (reg y) (reg z)
  | (NonTail(x), And(y, C(z))) -> 
     limm oc reg_imm z;
     op3 oc "and" (reg x) (reg y) reg_imm
  | (NonTail(x), Sll(y, V(z))) -> 
     op3 oc "sll" (reg x) (reg y) (reg z)
  | (NonTail(x), Sll(y, C(z))) -> 
     limm oc reg_imm z;
     op3 oc "sll" (reg x) (reg y) reg_imm
  | (NonTail(x), Srl(y, V(z))) -> 
     op3 oc "srl" (reg x) (reg y) (reg z)
  | (NonTail(x), Srl(y, C(z))) -> 
     limm oc reg_imm z;
     op3 oc "srl" (reg x) (reg y) reg_imm
  | (NonTail(x), Ldw(y, V(z))) ->
     op3 oc "add" reg_tmp (reg y) (reg z);
     op3 oc "ldw" (reg x) reg_tmp reg_zero
  | (NonTail(x), Ldw(y, C(z))) -> 
     limm oc reg_imm z;
     op3 oc "add" reg_imm (reg y) reg_imm;
     op3 oc "ldw" (reg x) reg_imm reg_zero
  | (NonTail(_), Stw(x, y, V(z))) ->
     op3 oc "add" reg_imm (reg y) (reg z);
     op3 oc "stw" reg_imm (reg x) reg_zero
  | (NonTail(_), Stw(x, y, C(z))) -> 
     limm oc reg_imm z;
     op3 oc "add" reg_imm (reg y) reg_imm;
     op3 oc "stw" reg_imm (reg x) reg_zero
  | (NonTail(x), FMr(y)) when x = y -> ()
  | (NonTail(x), FMr(y)) ->
     op3 oc "or" (reg x) (reg y) reg_zero
  | (NonTail(x), FAdd(y, z)) -> 
     op3 oc "fadd" (reg x) (reg y) (reg z)
  | (NonTail(x), FMul(y, z)) -> 
     op3 oc "fmul" (reg x) (reg y) (reg z)
  | (NonTail(x), FDiv(y, z)) -> 
     op3 oc "finv" reg_imm (reg z) reg_zero;
     op3 oc "fmul" (reg x) (reg y) reg_imm
  | (NonTail(x), Sqrt(y)) -> 
     op3 oc "fsqrt" (reg x) (reg y) reg_zero
  | (NonTail(x), Lfd(y, V(z))) ->
     op3 oc "add" reg_tmp (reg y) (reg z);
     op3 oc "ldw" (reg x) reg_tmp reg_zero
  | (NonTail(x), Lfd(y, C(z))) -> 
     limm oc reg_imm z;
     op3 oc "add" reg_imm (reg y) reg_imm;
     op3 oc "ldw" (reg x) reg_imm reg_zero
  | (NonTail(_), Stfd(x, y, V(z))) ->
     op3 oc "add" reg_imm (reg y) (reg z);
     op3 oc "stw" reg_imm (reg x) reg_zero
  | (NonTail(_), Stfd(x, y, C(z))) -> 
     limm oc reg_imm z;
     op3 oc "add" reg_imm (reg y) reg_imm;
     op3 oc "stw" reg_imm (reg x) reg_zero
  | (NonTail(x), ToFloat(y)) -> 
     op3 oc "or" (reg x) (reg y) reg_zero
  | (NonTail(x), ToInt(y)) -> 
     op3 oc "or" (reg x) (reg y) reg_zero
  | (NonTail(x), ToArray(y)) -> 
     op3 oc "or" (reg x) (reg y) reg_zero
  | (NonTail(x), In) -> 
     op1 oc "in" (reg x) 0
  | (NonTail(x), Out(y)) -> 
     op1 oc "out" (reg y) 0
  | (NonTail(x), GetHp) -> 
     op3 oc "or" (reg x) (reg reg_hp) reg_zero
  | (NonTail(x), SetHp(y)) -> 
     op3 oc "or" (reg reg_hp) (reg y) reg_zero
  | (NonTail(_), Comment(s)) -> Printf.fprintf oc "#\t%s\n" s
  (* 退避の仮想命令の実装 *)
  | (NonTail(_), Save(x, y))
       when not (S.mem y !stackset) ->
     save y;
(*Printf.fprintf oc "save %s,%d\n" y (offset y);*)
     limm oc reg_imm (offset y);
     op3 oc "add" reg_tmp reg_sp reg_imm;
     op3 oc "stw" reg_tmp (reg x) reg_zero
  | (NonTail(_), Save(x, y)) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 *)
  | (NonTail(x), Restore(y)) ->
(*Printf.fprintf oc "restore %s,%d\n" y (offset y);*)
     limm oc reg_imm (offset y);
     op3 oc "add" reg_tmp reg_sp reg_imm;
     op3 oc "ldw" (reg x) reg_tmp reg_zero
  (* 末尾だったら計算結果を第一レジスタにセット *)
  | (Tail, (Nop | Stw _ | Stfd _ | Comment _ | Save _ as exp)) ->
     g' oc (NonTail(Id.gentmp Type.Unit), exp);
     op3 oc "jr" reg_tmp reg_lr reg_zero
  | (Tail, (Li _ | SetL _ | Mr _ | Add _ | Sub _ | Xor _ | Or _ | And _ | Sll _ | Srl _ | Ldw _ | In | Out _ | GetHp | SetHp _ | ToInt _ | ToArray _ as exp)) -> 
     g' oc (NonTail(regs.(0)), exp);
     op3 oc "jr" reg_tmp reg_lr reg_zero
  | (Tail, (FLi _ | FMr _ | FAdd _ | FMul _ | FDiv _ | Sqrt _ | ToFloat _ | Lfd _ as exp)) ->
     g' oc (NonTail(fregs.(0)), exp);
     op3 oc "jr" reg_tmp reg_lr reg_zero
  | (Tail, (Restore(x) as exp)) ->
     (match locate x with
	    | [i] -> g' oc (NonTail(regs.(0)), exp)
	    | [i; j] when (i + 1 = j) -> g' oc (NonTail(fregs.(0)), exp)
	    | _ -> assert false);
     op3 oc "jr" reg_tmp reg_lr reg_zero
  | (Tail, IfEq(x, V(y), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg y);
     g'_tail_if oc e1 e2 "jreq" "jrneq"
  | (Tail, IfEq(x, C(y), e1, e2)) ->
     limm oc reg_imm y;
     op3 oc "cmp" reg_cond (reg x) reg_imm;
     g'_tail_if oc e1 e2 "jreq" "jrneq"
  | (Tail, IfLE(x, V(y), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg y);
     g'_tail_if oc e1 e2 "jrle" "jrgt"
  | (Tail, IfLE(x, C(y), e1, e2)) ->
     limm oc reg_imm y;
     op3 oc "cmp" reg_cond (reg x) reg_imm;
     g'_tail_if oc e1 e2 "jrle" "jrgt"
  | (Tail, IfGE(x, V(y), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg y);
     g'_tail_if oc e1 e2 "jrge" "jrlt"
  | (Tail, IfGE(x, C(y), e1, e2)) ->
     limm oc reg_imm y;
     op3 oc "cmp" reg_cond (reg x) reg_imm;
     g'_tail_if oc e1 e2 "jrge" "jrlt"
  | (Tail, IfFEq(x, y, e1, e2)) ->
     op3 oc "fcmp" reg_cond (reg x) (reg y);
     g'_tail_if oc e1 e2 "jreq" "jrneq"
  | (Tail, IfFLE(x, y, e1, e2)) ->
     op3 oc "fcmp" reg_cond (reg x) (reg y);
     g'_tail_if oc e1 e2 "jrle" "jrgt"
  | (NonTail(z), IfEq(x, V(y), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg y);
     g'_non_tail_if oc (NonTail(z)) e1 e2 "jreq" "jrneq"
  | (NonTail(z), IfEq(x, C(y), e1, e2)) ->
     limm oc reg_imm y;
     op3 oc "cmp" reg_cond (reg x) reg_imm;
     g'_non_tail_if oc (NonTail(z)) e1 e2 "jreq" "jrneq"
  | (NonTail(z), IfLE(x, V(y), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg y);
     g'_non_tail_if oc (NonTail(z)) e1 e2 "jrle" "jrgt"
  | (NonTail(z), IfLE(x, C(y), e1, e2)) ->
     limm oc reg_imm y;
     op3 oc "cmp" reg_cond (reg x) reg_imm;
     g'_non_tail_if oc (NonTail(z)) e1 e2 "jrle" "jrgt"
  | (NonTail(z), IfGE(x, V(y), e1, e2)) ->
     op3 oc "cmp" reg_cond (reg x) (reg y);
     g'_non_tail_if oc (NonTail(z)) e1 e2 "jrge" "jrlt"
  | (NonTail(z), IfGE(x, C(y), e1, e2)) ->
     limm oc reg_imm y;
     op3 oc "cmp" reg_cond (reg x) reg_imm;
     g'_non_tail_if oc (NonTail(z)) e1 e2 "jrge" "jrlt"
  | (NonTail(z), IfFEq(x, y, e1, e2)) ->
     op3 oc "fcmp" reg_cond (reg x) (reg y);
     g'_non_tail_if oc (NonTail(z)) e1 e2 "jreq" "jrneq"
  | (NonTail(z), IfFLE(x, y, e1, e2)) ->
     op3 oc "fcmp" reg_cond (reg x) (reg y);
     g'_non_tail_if oc (NonTail(z)) e1 e2 "jrle" "jrgt"
  (* 関数呼び出しの仮想命令の実装 *)
  | (Tail, CallCls(x, ys, zs)) -> (* 末尾呼び出し *)
     g'_args oc [(x, reg_cl)] ys zs;
     op3 oc "ldw" (reg reg_sw) (reg reg_cl) reg_zero;
     op3 oc "jr" reg_tmp (reg reg_sw) reg_zero
  | (Tail, CallDir(Id.L(x), ys, zs)) -> (* 末尾呼び出し *)
     g'_args oc [] ys zs;
     llabel oc reg_imm x;
     op3 oc "jr" reg_tmp reg_imm reg_zero
  | (NonTail(a), CallCls(x, ys, zs)) ->
     op3 oc "or" reg_tmp reg_lr reg_zero;
     g'_args oc [(x, reg_cl)] ys zs;
     let ss = stacksize () in
     limm oc reg_imm (ss - 1);
     op3 oc "add" reg_imm reg_sp reg_imm;
     op3 oc "stw" reg_imm reg_tmp reg_zero;
     limm oc reg_imm ss;
     op3 oc "add" reg_sp reg_sp reg_imm;
     op3 oc "ldw"reg_tmp (reg reg_cl) reg_zero;
     op3 oc "jr" reg_lr reg_tmp reg_zero;
     limm oc reg_imm ss;
     op3 oc "sub" reg_sp reg_sp reg_imm;
     limm oc reg_imm (ss - 1);
     op3 oc "add" reg_tmp reg_sp reg_imm;
     op3 oc "ldw" reg_tmp reg_tmp reg_zero;
	   (if List.mem a allregs && a <> regs.(0) then 
        op3 oc "or" (reg a) (reg regs.(0)) reg_zero
	    else if List.mem a allfregs && a <> fregs.(0) then 
        op3 oc "or" (reg a) (reg fregs.(0)) reg_zero);
     op3 oc "or" reg_lr reg_tmp reg_zero
  | (NonTail(a), CallDir(Id.L(x), ys, zs)) -> 
     op3 oc "or" reg_tmp reg_lr reg_zero;
     g'_args oc [] ys zs;
     let ss = stacksize () in
     limm oc reg_imm (ss - 1);
     op3 oc "add" reg_imm reg_sp reg_imm;
     op3 oc "stw" reg_imm reg_tmp reg_zero;
     limm oc reg_imm ss;
     op3 oc "add" reg_sp reg_sp reg_imm;
     llabel oc reg_imm x;
     op3 oc "jr" reg_lr reg_imm reg_zero;
     limm oc reg_imm ss;
     op3 oc "sub" reg_sp reg_sp reg_imm;
     limm oc reg_imm (ss - 1);
     op3 oc "add" reg_tmp reg_sp reg_imm;
     op3 oc "ldw" reg_tmp reg_tmp reg_zero;
	   (if List.mem a allregs && a <> regs.(0) then
        op3 oc "or" (reg a) (reg regs.(0)) reg_zero
	    else if List.mem a allfregs && a <> fregs.(0) then
        op3 oc "or" (reg a) (reg fregs.(0)) reg_zero);
     op3 oc "or" reg_lr reg_tmp reg_zero
and g'_tail_if oc e1 e2 b bn = 
  let b_else = Id.genid (b ^ "_else") in
  llabel oc reg_imm b_else;
  op3 oc bn reg_tmp reg_cond reg_imm;
  let stackset_back = !stackset in
  g oc (Tail, e1);
  Printf.fprintf oc "%s:\n" b_else;
  stackset := stackset_back;
  g oc (Tail, e2)
and g'_non_tail_if oc dest e1 e2 b bn = 
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
  llabel oc reg_imm b_else;
  op3 oc bn reg_tmp reg_cond reg_imm;
  let stackset_back = !stackset in
  g oc (dest, e1);
  let stackset1 = !stackset in
  llabel oc reg_imm b_cont;
  op3 oc "jr" reg_tmp reg_imm reg_zero;
	Printf.fprintf oc "%s:\n" b_else;
	stackset := stackset_back;
	g oc (dest, e2);
	Printf.fprintf oc "%s:\n" b_cont;
	let stackset2 = !stackset in
	stackset := S.inter stackset1 stackset2
and g'_args oc x_reg_cl ys zs = 
  let (i, yrs) = 
    List.fold_left
      (fun (i, yrs) y -> (i + 1, (y, regs.(i)) :: yrs))
      (0, x_reg_cl) ys in
  List.iter
    (fun (y, r) -> op3 oc "or" (reg r) (reg y) reg_zero)
    (shuffle reg_sw yrs);
  let (d, zfrs) = 
    List.fold_left
	    (fun (d, zfrs) z -> (d + 1, (z, fregs.(d)) :: zfrs))
	    (0, []) zs in
  List.iter
    (fun (z, fr) -> op3 oc "or" (reg fr) (reg z) reg_zero)
	  (shuffle reg_fsw zfrs)

let h oc { name = Id.L(x); args = _; fargs = _; body = e; ret = _ } =
  Printf.fprintf oc "%s:\n" x;
  stackset := S.empty;
  stackmap := [];
  g oc (Tail, e)

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
  | Li(i) ->
     Printf.fprintf stdout "li %d\n" i
  | FLi(Id.L(l)) ->
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
  | CallCls(x, ys, zs) ->
     Printf.fprintf stdout "callcls %s, " x;
     Printf.fprintf stdout "ys:";
     List.iter (fun y -> Printf.fprintf stdout "%s, " y) ys;
     Printf.fprintf stdout "zs:";
     List.iter (fun y -> Printf.fprintf stdout "%s, " y) zs;
     Printf.fprintf stdout "\n"
  | CallDir(Id.L(x), ys, zs) -> 
     Printf.fprintf stdout "calldir %s, " x;
     Printf.fprintf stdout "ys:";
     List.iter (fun y -> Printf.fprintf stdout "%s, " y) ys;
     Printf.fprintf stdout "zs:";
     List.iter (fun y -> Printf.fprintf stdout "%s, " y) zs;
     Printf.fprintf stdout "\n"

let f oc (Prog(data, vars, fundefs, e)) =
  (*List.iter (fun {name= Id.L(name); args=_; fargs=_; body= e; ret=r} -> print_string (name^":\n"); i "" (Tail, e)) fundefs;
  print_string "min_caml_start:\n";
  i "" (NonTail("r08"), e);*)
  Format.eprintf "generating assembly...@.";
  Printf.fprintf oc "\t.text\n";
  Printf.fprintf oc "\t.globl  _min_caml_init\n";
  Printf.fprintf oc "\t.align 2\n";
  llabel oc reg_imm "_min_caml_init";
  op3 oc "jr" reg_tmp reg_imm reg_zero;
  (if data <> [] then
    (Printf.fprintf oc "\t.data\n\t.literal8\n";
     List.iter
       (fun (Id.L(x), d) ->
	      Printf.fprintf oc "\t.align 3\n";
	      Printf.fprintf oc "%s:\t # %f\n" x d;
	      Printf.fprintf oc "\t.long\t%fd\n" d)
       data));
  Printf.fprintf oc "\t.text\n";
  Printf.fprintf oc "\t.align 2\n";
  List.iter (fun fundef -> h oc fundef) fundefs;
  Printf.fprintf oc "_min_caml_init: # main entry point\n";
  Printf.fprintf oc "   # stack start from 2MB\n";
  limm oc reg_sp ((2*1024*1024)/4);
  Printf.fprintf oc "   # heap start from 0\n";
  limm oc (reg reg_hp) 0;
  Printf.fprintf oc "   # main program start\n";
  Printf.fprintf oc "_min_caml_start: # main entry point\n";
  stackset := S.empty;
  stackmap := [];
  g oc (NonTail("r08"), e);
  op1 oc "hlt" reg_zero 0;
  Printf.fprintf oc "   # main program end\n";
