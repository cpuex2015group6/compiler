(* cpuex assembly with a few virtual instructions *)

type id_or_imm = V of Id.t | C of int
type l_or_imm = L of Id.l | C of int
type t = (* 命令の列 *)
  | Ans of exp
  | Let of (Id.t * Type.t) * exp * t
and exp = (* 一つ一つの命令に対応する式 *)
  | Nop
  | Li of l_or_imm
  | FLi of l_or_imm
  | SetL of Id.l
  | Mr of Id.t
  | Add of Id.t * id_or_imm
  | Sub of Id.t * id_or_imm
  | Xor of Id.t * id_or_imm
  | Or of Id.t * id_or_imm
  | And of Id.t * id_or_imm
  | Sll of Id.t * id_or_imm
  | Srl of Id.t * id_or_imm
  | Ldw of Id.t * id_or_imm
  | Stw of Id.t * Id.t * id_or_imm
  | FMr of Id.t
  | FAdd of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | FAbs of Id.t
  | Sqrt of Id.t
  | Lfd of Id.t * id_or_imm
  | Stfd of Id.t * Id.t * id_or_imm
  | ToInt of Id.t
  | ToFloat of Id.t
  | ToArray of Id.t
  | In
  | Out of Id.t
  | Count
  | ShowExec
  | SetCurExec
  | GetExecDiff
  | GetHp
  | SetHp of Id.t
  | Comment of string
  (* virtual instructions *)
  | IfEq of Id.t * id_or_imm * t * t
  | IfLE of Id.t * id_or_imm * t * t
  | IfGE of Id.t * id_or_imm * t * t
  | IfFEq of Id.t * Id.t * t * t
  | IfFLE of Id.t * Id.t * t * t
  (* closure address, integer arguments, and float arguments *)
  | CallCls of Id.t * Id.t list
  | CallDir of Id.l * Id.t list
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of Id.t (* スタック変数から値を復元 *)
type fundef =
    { name : Id.l; args : Id.t list; body : t; ret : Type.t }
(* プログラム全体 = 浮動小数点数テーブル + グローバル変数テーブル + トップレベル関数 + メインの式 *)
type prog = Prog of (Id.l * int) list * Id.l list * fundef list * t

(* shorthand of Let for float *)
(* fletd : Id.t * exp * t -> t *)
let fletd (x, e1, e2) = Let ((x, Type.Float), e1, e2)
(* shorthand of Let for unit *)
(* seq : exp * t -> t *)
let seq (e1, e2) = Let ((Id.gentmp Type.Unit, Type.Unit), e1, e2)

let regs = [| "%r08"; "%r09"; "%r0A"; "%r0B"; "%r0C"; "%r0D"; "%r0E"; "%r0F";
              "%r10"; "%r11"; "%r12"; "%r13"; "%r14"; "%r15"; "%r16"; "%r17";
	      "%r18"; "%r19"; "%r1A"; "%r1B"; "%r1C"; "%r1D"; "%r1E"; |]
let allregs = Array.to_list regs
let reg_cl = regs.(Array.length regs - 1) (* closure address *)
let reg_sw = regs.(Array.length regs - 2) (* temporary for swap *)
let reg_hp = "%r04"
let reg_sp = "r03"
let reg_tmp = "r05"
let reg_imm = "r06"
let reg_cond = "r07"
let reg_lr = "r02"
let reg_zero = "%rFF"
let heap_start = 256
let stack_start = ((2*1024*1024)/4)

(* is_reg : Id.t -> bool *)
let is_reg x = x.[0] = '%'

(* remove_and_uniq : S.t -> Id.t list -> Id.t list *)
let rec remove_and_uniq xs = function 
  | [] -> []
  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys

(* free variables in the order of use (for spilling) *)
(* fv_id_or_imm : id_or_imm -> Id.t list *)
let fv_id_or_imm = function V (x) -> [x] | _ -> []

let rec fv_let x exp e =
  exp @ remove_and_uniq (S.singleton x) e

let rec fv_if x y' e1 e2 =
    x :: fv_id_or_imm y' @ remove_and_uniq S.empty (e1 @ e2)

let rec fv_iff x y e1 e2 =
    x :: y :: remove_and_uniq S.empty (e1 @ e2)

let rec fv_exp = function
  | Nop | In | Count | ShowExec | SetCurExec | GetExecDiff | GetHp | Li (_) | FLi (_) | SetL (_) | Comment (_) | Restore (_) -> []
  | Mr (x) | FMr (x) | FAbs(x) | Save (x, _) | Sqrt (x) | ToFloat(x) | ToInt(x) | ToArray(x) | Out (x) | SetHp (x) -> [x]
  | Add (x, y') | Sub (x, y') | Xor (x, y') | Or (x, y') | And (x, y') | Sll (x, y') | Srl (x, y') |  Lfd (x, y') | Ldw (x, y') -> 
      x :: fv_id_or_imm y'
  | FAdd (x, y) | FMul (x, y) | FDiv (x, y) ->
      [x; y]
  | Stw (x, y, z') | Stfd (x, y, z') -> x :: y :: fv_id_or_imm z'
  | IfEq (x, y', e1, e2) | IfLE (x, y', e1, e2) | IfGE (x, y', e1, e2) ->
     fv_if x y' (fv_o e1) (fv_o e2)
  | IfFEq (x, y, e1, e2) | IfFLE (x, y, e1, e2) ->
     fv_iff x y (fv_o e1) (fv_o e2)
  | CallCls (x, ys) -> x :: ys
  | CallDir (_, ys) -> ys
and fv_o = function 
  | Ans (exp) -> fv_exp exp
  | Let ((x, t), exp, e) ->
     fv_let x (fv_exp exp) (fv_o e)

(* fv : t -> Id.t list *)
let fv e = remove_and_uniq S.empty (fv_o e)
				
(* concat : t -> Id.t * Type.t -> t -> t *)
let rec concat e1 xt e2 = match e1 with
  | Ans (exp) -> Let (xt, exp, e2)
  | Let (yt, exp, e1') -> Let (yt, exp, concat e1' xt e2)


type vars =
  | Pair of Id.t list * Id.t * vars
  | List of Id.t list
let rec concatfv_sub e1 (x, t) e2 = match e1 with
  | Let ((y, t'), exp, e1') -> Pair((fv_exp exp), y, (concatfv_sub e1' (x, t) e2))
  | Ans (exp) -> Pair ((fv_exp exp), x, (List e2))

let rec remove_and_uniq_fv xs ys =
  match ys with
  | List(xss) ->
     remove_and_uniq xs xss
  | Pair([], r, ys') ->
     remove_and_uniq_fv (S.add r xs) ys'
  | Pair(x :: xss, r, ys) when S.mem x xs ->
     remove_and_uniq_fv xs (Pair(xss, r, ys))
  | Pair(x :: xss, r, ys) ->
     x :: remove_and_uniq_fv (S.add x xs) (Pair(xss, r, ys))
     
(* concatfv : t -> Id.t * Type.t -> Id.t list -> Id.t list *)
let rec concatfv e1 xt e2 =
  remove_and_uniq_fv S.empty (concatfv_sub e1 xt e2) 

(* align : int -> int *)
let align i = i

(* デバッグ用 *)
type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 *)

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
  print_endline ">>>>>>>>>>>>>>>>assmbly>>>>>>>>>>>>>>>>>";
  List.iter (fun {name= Id.L(name); args=_; body= e; ret=r} -> print_string (name^":\n"); i "" (Tail, e)) fundefs;
  print_endline "min_caml_start:";
  i "" (NonTail("r08"), e)
