(* cpuex assembly with a few virtual instructions *)

type id_or_imm = V of Id.t | C of int
type l_or_imm = L of Id.l | C of int
type t = (* 命令の列 *)
  | Ans of exp
  | Let of (Id.t * Type.t) list * exp * t
and exp = (* 一つ一つの命令に対応する式 *)
  | Nop
  | Li of l_or_imm
  | SetL of Id.l
  | Mr of Id.t
  | Tuple of Id.t list
  | Add of Id.t * id_or_imm
  | Sub of Id.t * id_or_imm
  | Xor of Id.t * id_or_imm
  | Or of Id.t * id_or_imm
  | And of Id.t * id_or_imm
  | Sll of Id.t * id_or_imm
  | Srl of Id.t * id_or_imm
  | Ldw of Id.t * id_or_imm
  | Stw of Id.t * Id.t * id_or_imm
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | FAbA of Id.t * Id.t
  | FAbs of Id.t
  | Sqrt of Id.t
  | In
  | Out of Id.t
  | Count
  | ShowExec
  | SetCurExec
  | GetExecDiff
  | GetHp
  | SetHp of id_or_imm
  | Comment of string
  | Cmp of int * Id.t * id_or_imm
  | FCmp of int * Id.t * Id.t
  | Cmpa of int * Id.t * id_or_imm * Id.t
  | FCmpa of int * Id.t * Id.t * Id.t
  (* virtual instructions *)
  | If of int * Id.t * Id.t * t * t
  | FIf of int * Id.t * Id.t * t * t
  | IfThen of Id.t * t * Id.t list
  | CallCls of Id.t * Id.t list
  | CallDir of Id.l * Id.t list
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of Id.t (* スタック変数から値を復元 *)
type fundef =
    { name : Id.l; args : Id.t list; body : t; ret : Type.t }
(* プログラム全体 = 浮動小数点数テーブル + グローバル変数テーブル + トップレベル関数 + メインの式 *)
type prog = Prog of (Id.l * int) list * Id.l list * fundef list * t

let negcond c = c lxor 7
let swapcond c = (if c land 1 <> 0 then 4 else 0) lor (if c land 2 <> 0 then 2 else 0) lor (if c land 4 <> 0 then 1 else 0)
    
(* shorthand of Let for unit *)
(* seq : exp * t -> t *)
let seq (e1, e2) = Let ([(Id.gentmp Type.Unit, Type.Unit)], e1, e2)

let regs = [| "%r07"; "%r08"; "%r09"; "%r0A"; "%r0B"; "%r0C"; "%r0D"; "%r0E"; "%r0F";
              "%r10"; "%r11"; "%r12"; "%r13"; "%r14"; "%r15"; "%r16"; "%r17";
	      "%r18"; "%r19"; "%r1A"; "%r1B"; "%r1C"; "%r1D"; "%r1E"; |]
let allregs = Array.to_list regs
let reg_cl = regs.(Array.length regs - 1) (* closure address *)
let reg_sw = regs.(Array.length regs - 2) (* temporary for swap *)
let reg_hp = "%r04"
let reg_sp = "r03"
let reg_tmp = "r05"
let reg_imm = "r06"
let reg_lr = "r02"
let reg_zero = "%r1F"
let reg_m1 = "%r01"
let heap_start = 256
let stack_start = ((2*1024*1024)/4)

(* is_reg : Id.t -> bool *)
let is_reg x = x.[0] = '%'

(* rm_t : (Id.t * Type.t) list -> Id.t list *)
let rm_t = List.fold_left (fun l (x, _) -> l@[x]) []
(* rm_x : (Id.t * Type.t) list -> Type.t list *)
let rm_x = List.fold_left (fun l (_, t) -> l@[t]) []
(* unify_xt : Id.t list ->  Type.t list -> (Id.t * Type.t) list *)
let unify_xt = List.fold_left2 (fun l x t -> l@[(x, t)]) []
  
(* remove_and_uniq : S.t -> Id.t list -> Id.t list *)
let rec remove_and_uniq xs = function 
  | [] -> []
  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys

(* free variables in the order of use (for spilling) *)
(* fv_id_or_imm : id_or_imm -> Id.t list *)
let fv_id_or_imm = function V (x) -> [x] | _ -> []

let rec fv_let xs exp e =
  exp @ remove_and_uniq (S.of_list xs) e

let rec fv_if x y e1 e2 =
    x :: y :: remove_and_uniq S.empty (e1 @ e2)

let rec fv_ifthen f e t =
  f :: remove_and_uniq S.empty (e @ t)

let rec fv_exp = function
  | Nop | In | Count | ShowExec | SetCurExec | GetExecDiff | GetHp | Li (_) | SetL (_) | Comment (_) | Restore (_) -> []
  | Mr (x) | FAbs(x) | Save (x, _) | Sqrt (x) | Out (x) -> [x]
  | Tuple(xs) -> xs
  | SetHp (x) -> fv_id_or_imm x
  | Add (x, y') | Sub (x, y') | Xor (x, y') | Or (x, y') | And (x, y') | Sll (x, y') | Srl (x, y') | Ldw (x, y') | Cmp (_, x, y') -> 
     x :: fv_id_or_imm y'
  | Cmpa (_, x, y', z) ->
     x :: z :: fv_id_or_imm y'
  | FAdd (x, y) | FSub (x, y) | FMul (x, y) | FDiv (x, y) | FAbA (x, y) | FCmp(_, x, y) ->
     [x; y]
  | FCmpa (_, x, y, z) ->
     [x; y; z]
  | Stw (x, y, z') -> x :: y :: fv_id_or_imm z'
  | If (_, x, y, e1, e2) | FIf (_, x, y, e1, e2) ->
     fv_if x y (fv_o e1) (fv_o e2)
  | IfThen (f, e, t) ->
     fv_ifthen f (fv_o e) t
  | CallCls (x, ys) -> x :: ys
  | CallDir (_, ys) -> ys
and fv_o = function 
  | Ans (exp) -> fv_exp exp
  | Let (xts, exp, e) ->
     fv_let (rm_t xts) (fv_exp exp) (fv_o e)

(* fv : t -> Id.t list *)
let fv e = remove_and_uniq S.empty (fv_o e)

(* rm_t_s : (Id.t * Type.t) list -> S.t *)
let rm_t_s = List.fold_left (fun s (x, _) -> S.add x s) S.empty

(* free variables in the order of use (for spilling) *)
(* fvs_id_or_imm : id_or_imm -> S.t *)
let fvs_id_or_imm = function V (x) -> S.singleton x | _ -> S.empty

let rec fvs_let xs exp e =
  S.union exp (List.fold_left (fun s x -> S.remove x s) e xs)

let rec fvs_if x y e1 e2 =
  S.add x (S.add y (S.union e1 e2))

let rec fvs_ifthen f e t =
  S.add f (S.union e (S.of_list t))

let rec fvs_exp = function
  | Nop | In | Count | ShowExec | SetCurExec | GetExecDiff | GetHp | Li (_) | SetL (_) | Comment (_) | Restore (_) -> S.empty
  | Mr (x) | FAbs(x) | Save (x, _) | Sqrt (x) | Out (x) -> S.singleton x
  | Tuple(xs) -> S.of_list xs
  | SetHp (x) -> fvs_id_or_imm x
  | Add (x, y') | Sub (x, y') | Xor (x, y') | Or (x, y') | And (x, y') | Sll (x, y') | Srl (x, y') | Ldw (x, y') | Cmp (_, x, y') -> 
     S.add x (fvs_id_or_imm y')
  | Cmpa (_, x, y', z) ->
     S.add x (S.add z (fvs_id_or_imm y'))
  | FAdd (x, y) | FSub (x, y) | FMul (x, y) | FDiv (x, y) | FAbA (x, y) | FCmp(_, x, y)  ->
     S.add x (S.singleton y)
  | FCmpa (_, x, y, z) ->
     S.add x (S.add y (S.singleton z))
  | Stw (x, y, z') -> S.add x (S.add y (fvs_id_or_imm z'))
  | If (_, x, y, e1, e2) | FIf (_, x, y, e1, e2) ->
     fvs_if x y (fvs e1) (fvs e2)
  | IfThen (f, e, t) ->
     fvs_ifthen f (fvs e) t
  | CallCls (x, ys) -> S.add x (S.of_list ys)
  | CallDir (_, ys) -> S.of_list ys
(* fvs : t -> S.t *)
and fvs = function 
  | Ans (exp) -> fvs_exp exp
  | Let (xts, exp, e) ->
     fvs_let (rm_t xts) (fvs_exp exp) (fvs e)
       
(* concatfvs : t -> (Id.t * Type.t) list -> S.t -> S.t *)
(* Let(xt, e1, e2) した時のfree variablesのSet *)
let rec concatfvs e1 xts e2 = match e1 with
  | Ans(exp) ->
     fvs_let (rm_t xts) (fvs_exp exp) e2
  | Let(yts, exp, e1') ->
     fvs_let (rm_t yts) (fvs_exp exp) (concatfvs e1' xts e2)

(* lconcatfvs : t -> (Id.t * Type.t) list -> S.t -> S.t *)
let rec lconcatfvs e1 xts e2 = match e1 with
  | Ans(CallCls _ as exp) | Ans(CallDir _ as exp)
  | Let(_, (CallCls _ as exp), _) | Let(_, (CallDir _ as exp), _) ->
     fvs_exp exp
  | Ans(exp) ->
     fvs_let (rm_t xts) (fvs_exp exp) e2
  | Let(yts, exp, e1') ->
     fvs_let (rm_t yts) (fvs_exp exp) (lconcatfvs e1' xts e2)

(* concatfvs' : t -> (Id.t * Type.t) list -> S.t -> S.t -> S.t *)
(* concatfvsとlconcatfvsを同時に呼び出す *)
let rec concatfvs' e1 xts e2 le2 = (concatfvs e1 xts e2), (lconcatfvs e1 xts le2)

(* concat : t -> (Id.t * Type.t) list -> t -> t *)
let rec concat e1 xts e2 = match e1 with
  | Ans (exp) -> Let (xts, exp, e2)
  | Let (yts, exp, e1') -> Let (yts, exp, concat e1' xts e2)

let is_ereg r = is_reg r && (r = reg_zero || r = reg_m1)

let rec effect = function (* 副作用の有無 *)
  | If(_, x, y, e1, e2) | FIf(_, x, y, e1, e2) -> is_ereg x || is_ereg y || effect' e1 || effect' e2
  | IfThen(f, e, t) -> is_ereg f || effect' e || effect (Tuple(t))
  | Stw _ | In | Out _ | Count | ShowExec | SetCurExec | GetExecDiff | SetHp _ | Comment _ | CallCls _ | CallDir _ | Save _ | Restore _ -> true
  | Ldw _ | Nop | Li _ | SetL _ | GetHp -> false
  | Mr(x) | FAbs(x) | Sqrt(x) -> is_ereg x
  | Tuple(xs) -> List.fold_left (fun f x -> f || is_ereg x) false xs
  | Add(x, y) | Sub(x, y) | Xor(x, y) | Or(x, y) | And(x, y) | Sll(x, y) | Srl(x, y) | Cmp(_, x, y) -> is_ereg x || (match y with | C(_) -> false | V(y) -> is_ereg y)
  | Cmpa(_, x, y, z) -> is_ereg x || (match y with | C(_) -> false | V(y) -> is_ereg y) || is_ereg z
  | FAdd(x, y) | FSub(x, y) | FMul(x, y) | FDiv(x, y) | FAbA(x, y) | FCmp(_, x, y) -> is_ereg x || is_ereg y
  | FCmpa(_, x, y, z) -> is_ereg x || is_ereg y || is_ereg z
and effect' = function
  | Ans(exp) -> effect exp
  | Let(_, exp, e) -> effect exp || effect' e
     
(* concatfv : t -> (Id.t * Type.t) list -> Id.t list -> Id.t list *)
let rec concatfv e1 xts e2 = match e1 with
  | Ans(exp) ->
     remove_and_uniq S.empty (fv_let (rm_t xts) (fv_exp exp) e2)
  | Let(yts, exp, e1') ->
     remove_and_uniq S.empty (fv_let (rm_t yts) (fv_exp exp) (concatfv e1' xts e2))

(* align : int -> int *)
let align i = i

(* デバッグ用 *)
type dest = Tail | NonTail of Id.t list (* 末尾かどうかを表すデータ型 *)

let rec i indent = function
  | (dest, Ans (exp)) -> i' indent (dest, exp)
  | (dest, Let(xts, exp, e)) -> i' indent (NonTail (rm_t xts), exp); i indent (dest, e)
and i' indent = function
  | (NonTail(xs), exp) ->
     print_string indent;
    List.iter (fun x -> print_string (x^" ")) xs;
    print_string "<- ";
    j indent exp
  | (Tail, exp) ->
     print_string (indent^"_ <- ");
     j indent exp
and j indent = function
  | Nop ->
     Printf.fprintf stdout "nop\n"
  | Li(C(i)) ->
     Printf.fprintf stdout "li %d\n" i
  | Li(L(Id.L(l))) ->
     Printf.fprintf stdout "li %s\n" l
  | SetL(Id.L(y)) -> 
     Printf.fprintf stdout "setl %s\n" y
  | Mr(y) ->
     Printf.fprintf stdout "mr %s\n" y
  | Tuple(ys) ->
     Printf.fprintf stdout "tuple ";
    List.iter (fun y -> Printf.fprintf stdout "%s " y) ys;
    Printf.fprintf stdout "\n"
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
  | FAdd(y, z) -> 
     Printf.fprintf stdout "fadd %s, %s\n" y z
  | FSub(y, z) -> 
     Printf.fprintf stdout "fsub %s, %s\n" y z
  | FMul(y, z) -> 
     Printf.fprintf stdout "fmul %s, %s\n" y z
  | FDiv(y, z) -> 
     Printf.fprintf stdout "fdiv %s, %s\n" y z
  | FAbA(y, z) -> 
     Printf.fprintf stdout "faba %s, %s\n" y z
  | FAbs(y) -> 
     Printf.fprintf stdout "fabs %s\n" y
  | Sqrt(y) -> 
     Printf.fprintf stdout "sqrt %s\n" y
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
  | SetHp(V(y)) -> 
     Printf.fprintf stdout "sethp %s\n" y
  | SetHp(C(i)) -> 
     Printf.fprintf stdout "sethp %d\n" i
  | Comment(s) ->
     Printf.fprintf stdout "comment %s\n" s
  | Save(x, y) ->
     Printf.fprintf stdout "save %s, %s\n" y x
  | Restore(y) ->
     Printf.fprintf stdout "restore %s\n" y
  | Cmp(c, x, V(y)) ->
     Printf.fprintf stdout "cmp %d, %s, %s\n" c x y;
  | Cmp(c, x, C(const)) ->
     Printf.fprintf stdout "cmp %d, %s, %d\n" c x const;
  | FCmp(c, x, y) ->
     Printf.fprintf stdout "fcmp %d, %s, %s\n" c x y;
  | Cmpa(c, x, V(y), z) ->
     Printf.fprintf stdout "cmpa %d, %s, %s, %s\n" c x y z;
  | Cmpa(c, x, C(const), z) ->
     Printf.fprintf stdout "cmpa %d, %s, %d, %s\n" c x const z;
  | FCmpa(c, x, y, z) ->
     Printf.fprintf stdout "fcmpa %d, %s, %s, %s\n" c x y z;
  | If(c, x, y, e1, e2) ->
     Printf.fprintf stdout "if %d %s %s\n" c x y;
     let indent = indent ^ "  " in
     Printf.fprintf stdout "%sthen:\n" indent;
     let indent' = indent ^ "  " in
     i indent' (Tail, e1);
     Printf.fprintf stdout "%selse:\n" indent;
     i indent' (Tail, e2)
  | FIf(c, x, y, e1, e2) ->
     Printf.fprintf stdout "fif %d %s %s\n" c x y;
     let indent = indent ^ "  " in
     Printf.fprintf stdout "%sthen:\n" indent;
     let indent' = indent ^ "  " in
     i indent' (Tail, e1);
     Printf.fprintf stdout "%selse:\n" indent;
     i indent' (Tail, e2)
  | IfThen(f, e, t) ->
     Printf.fprintf stdout "ifthen %s\n" f;
     let indent = indent ^ "  " in
     Printf.fprintf stdout "%sthen:\n" indent;
     let indent' = indent ^ "  " in
     i indent' (Tail, e);
     Printf.fprintf stdout "%selse:\n" indent;
     print_string (indent^"_ <- ");
     List.iter (fun y -> Printf.fprintf stdout "%s " y) t;
     Printf.fprintf stdout "\n"
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
  print_endline ">>>>>>>>>>>>>>>>asm>>>>>>>>>>>>>>>>>";
  List.iter (fun {name= Id.L(name); args=_; body= e; ret=r} -> print_string (name^":\n"); i "" (Tail, e)) fundefs;
  print_endline "min_caml_start:";
  i "" (NonTail([regs.(0)]), e)
