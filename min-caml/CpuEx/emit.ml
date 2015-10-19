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
let offset x = 4 * List.hd (locate x)
let stacksize () = align ((List.length !stackmap + 1) * 4)

let reg r = 
  if is_reg r 
  then String.sub r 1 (String.length r - 1)
  else r 

let llabel oc r1 label =
  Printf.fprintf oc "\tlimm\t%s, %s\n" r1 label

let op3 oc inst r1 r2 r3 =
  Printf.fprintf oc "\t%s\t%s, %s, %s\n" inst r1 r2 r3

let limm oc r1 imm =
  let limm_sub oc r1 imm =
      Printf.fprintf oc "\tlimm\t%s, %d\n" r1 imm in
  match imm with
  | _ when imm >= -32768 && imm < 32768 -> 
     limm_sub oc r1 imm
  | _ ->
     let n = imm lsr 16 in
     let m = imm lxor (n lsl 16) in
     let r = r1 in
     limm_sub oc r n;
     limm_sub oc reg_imm 16;
     op3 oc "sll" r r reg_imm;
     limm_sub oc reg_imm m;
     op3 oc "or" r r reg_imm

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
  | (NonTail(x), FAdd(y, z)) -> 
     op3 oc "fadd" (reg x) (reg y) (reg z)
  | (NonTail(x), FMul(y, z)) -> 
     op3 oc "fmul" (reg x) (reg y) (reg z)
  | (NonTail(x), FDiv(y, z)) -> 
     op3 oc "fdiv" (reg x) (reg y) (reg z)
  | (NonTail(_), Comment(s)) -> Printf.fprintf oc "#\t%s\n" s
  (* 退避の仮想命令の実装 *)
  | (NonTail(_), Save(x, y))
       when not (S.mem y !stackset) ->
     save y;
     limm oc reg_imm (offset y);
     op3 oc "add" reg_tmp reg_sp reg_imm;
     op3 oc "stw" reg_tmp (reg x) reg_zero
  | (NonTail(_), Save(x, y)) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 *)
  | (NonTail(x), Restore(y)) ->
     limm oc reg_imm (offset y);
     op3 oc "add" reg_tmp reg_sp reg_imm;
     op3 oc "ldw" (reg x) reg_tmp reg_zero
  (* 末尾だったら計算結果を第一レジスタにセット *)
  | (Tail, (Nop | Stw _ | Comment _ | Save _ as exp)) ->
     g' oc (NonTail(Id.gentmp Type.Unit), exp);
     op3 oc "jr" reg_tmp reg_lr reg_zero
  | (Tail, (Li _ | SetL _ | Mr _ | Add _ | Sub _ | Xor _ | Sll _ | Srl _ |
            Ldw _ as exp)) -> 
     g' oc (NonTail(regs.(0)), exp);
     op3 oc "jr" reg_tmp reg_lr reg_zero
  | (Tail, (FLi _ | FAdd _ | FMul _ | FDiv _ as exp)) ->
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
     limm oc reg_imm (ss - 4);
     op3 oc "add" reg_imm reg_sp reg_imm;
     op3 oc "stw" reg_imm reg_tmp reg_zero;
     limm oc reg_imm ss;
     op3 oc "add" reg_sp reg_sp reg_imm;
     op3 oc "ldw"reg_tmp (reg reg_cl) reg_zero;
     op3 oc "jr" reg_tmp reg_tmp reg_zero;
     limm oc reg_imm ss;
     op3 oc "sub" reg_sp reg_sp reg_imm;
     limm oc reg_imm (ss - 4);
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
     limm oc reg_imm (ss - 4);
     op3 oc "add" reg_imm reg_sp reg_imm;
     op3 oc "stw" reg_imm reg_tmp reg_zero;
     limm oc reg_imm ss;
     op3 oc "add" reg_sp reg_sp reg_imm;
     llabel oc reg_imm x;
     op3 oc "or" reg_tmp reg_imm reg_zero;
     op3 oc "jr" reg_lr reg_tmp reg_zero;
     limm oc reg_imm ss;
     op3 oc "sub" reg_sp reg_sp reg_imm;
     limm oc reg_imm (ss - 4);
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

let f oc (Prog(data, fundefs, e)) =
  Format.eprintf "generating assembly...@.";
  Printf.fprintf oc "\t.text\n";
  Printf.fprintf oc "\t.globl  _min_caml_start\n";
  Printf.fprintf oc "\t.align 2\n";
  llabel oc reg_imm "_min_caml_start";
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
  Printf.fprintf oc "_min_caml_start: # main entry point\n";
  Printf.fprintf oc "   # stack start from 16MB - 5MB (11534336)\n";
  limm oc reg_sp ((16-5)*1024*1024);
  Printf.fprintf oc "   # heap start from 16MB - 4MB (12582912)\n";
  limm oc (reg reg_hp) ((16-4)*1024*1024);
  Printf.fprintf oc "   # main program start\n";
  stackset := S.empty;
  stackmap := [];
  g oc (NonTail("_R_00"), e);
  Printf.fprintf oc "   # main program end\n";
  llabel oc reg_imm "_min_caml_end";
	Printf.fprintf oc "_min_caml_end: # infinite loop\n";
  op3 oc "jr" reg_tmp reg_imm reg_zero
