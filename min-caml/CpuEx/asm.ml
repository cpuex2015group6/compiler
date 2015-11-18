(* PowerPC assembly with a few virtual instructions *)

type id_or_imm = V of Id.t | C of int
type t = (* 命令の列 *)
  | Ans of exp
  | Let of (Id.t * Type.t) * exp * t
and exp = (* 一つ一つの命令に対応する式 *)
  | Nop
  | Li of int
  | FLi of Id.l
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
  | Sqrt of Id.t
  | Lfd of Id.t * id_or_imm
  | Stfd of Id.t * Id.t * id_or_imm
  | ToInt of Id.t
  | ToFloat of Id.t
  | ToArray of Id.t
  | In
  | Out of Id.t
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
  | CallCls of Id.t * Id.t list * Id.t list
  | CallDir of Id.l * Id.t list * Id.t list
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of Id.t (* スタック変数から値を復元 *)
type fundef =
    { name : Id.l; args : Id.t list; fargs : Id.t list; body : t; ret : Type.t }
(* プログラム全体 = 浮動小数点数テーブル + グローバル変数テーブル + トップレベル関数 + メインの式 *)
type prog = Prog of (Id.l * float) list * Id.l list * fundef list * t

(* shorthand of Let for float *)
(* fletd : Id.t * exp * t -> t *)
let fletd (x, e1, e2) = Let ((x, Type.Float), e1, e2)
(* shorthand of Let for unit *)
(* seq : exp * t -> t *)
let seq (e1, e2) = Let ((Id.gentmp Type.Unit, Type.Unit), e1, e2)

let regs = [| "%r08"; "%r09"; "%r0A"; "%r0B"; "%r0C"; "%r0D"; "%r0E"; "%r0F";
              "%r10"; "%r11"; "%r12"; "%r13"; "%r14"; "%r15"; "%r16"; "%r17";

(*	      "%r20"; "%r21"; "%r22"; "%r23"; "%r24"; "%r25"; "%r26"; "%r27";
	      "%r28"; "%r29"; "%r2A"; "%r2B"; "%r2C"; "%r2D"; "%r2E"; "%r2F";
	      "%r40"; "%r41"; "%r42"; "%r43"; "%r44"; "%r45"; "%r46"; "%r47";
	      "%r48"; "%r49"; "%r4A"; "%r4B"; "%r4C"; "%r4D"; "%r4E"; "%r4F";
	      "%r50"; "%r51"; "%r52"; "%r53"; "%r54"; "%r55"; "%r56"; "%r57";
	      "%r58"; "%r59"; "%r5A"; "%r5B"; "%r5C"; "%r5D"; "%r5E"; "%r5F";
	      "%r60"; "%r61"; "%r62"; "%r63"; "%r64"; "%r65"; "%r66"; "%r67";
	      "%r68"; "%r69"; "%r6A"; "%r6B"; "%r6C"; "%r6D"; "%r6E"; "%r6F";*)
             |]
(* let regs = Array.init 27 (fun i -> Printf.sprintf "_R_%d" i) *)
let fregs = [| "%r18"; "%r19"; "%r1A"; "%r1B"; "%r1C"; "%r1D"; "%r1E";
(*	       "%r30"; "%r31"; "%r32"; "%r33"; "%r34"; "%r35"; "%r36"; "%r37";
	       "%r38"; "%r39"; "%r3A"; "%r3B"; "%r3C"; "%r3D"; "%r3E"; "%r3F";*)
              |]
let allregs = Array.to_list regs
let allfregs = Array.to_list fregs
let reg_cl = regs.(Array.length regs - 1) (* closure address *)
let reg_sw = regs.(Array.length regs - 2) (* temporary for swap *)
let reg_fsw = fregs.(Array.length fregs - 1) (* temporary for swap *)
let reg_hp = "%r04"
let reg_sp = "r03"
let reg_tmp = "r05"
let reg_imm = "r06"
let reg_cond = "r07"
let reg_lr = "r02"
let reg_zero = "rFF"

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

(* fv_exp : Id.t list -> t -> S.t list *)
let rec fv_exp = function
  | Nop | In | GetHp | Li (_) | FLi (_) | SetL (_) | Comment (_) | Restore (_) -> []
  | Mr (x) | FMr (x) | Save (x, _) | Sqrt (x) | ToFloat(x) | ToInt(x) | ToArray(x) | Out (x) | SetHp (x) -> [x]
  | Add (x, y') | Sub (x, y') | Xor (x, y') | Or (x, y') | And (x, y') | Sll (x, y') | Srl (x, y') |  Lfd (x, y') | Ldw (x, y') -> 
      x :: fv_id_or_imm y'
  | FAdd (x, y) | FMul (x, y) | FDiv (x, y) ->
      [x; y]
  | Stw (x, y, z') | Stfd (x, y, z') -> x :: y :: fv_id_or_imm z'
  | IfEq (x, y', e1, e2) | IfLE (x, y', e1, e2) | IfGE (x, y', e1, e2) -> 
      x :: fv_id_or_imm y' @ remove_and_uniq S.empty (fv_o e1 @ fv_o e2)
  | IfFEq (x, y, e1, e2) | IfFLE (x, y, e1, e2) ->
      x :: y :: remove_and_uniq S.empty (fv_o e1 @ fv_o e2)
  | CallCls (x, ys, zs) -> x :: ys @ zs
  | CallDir (_, ys, zs) -> ys @ zs
and fv_o = function 
  | Ans (exp) -> fv_exp exp
  | Let ((x, t), exp, e) ->
      fv_exp exp @ remove_and_uniq (S.singleton x) (fv_o e)

(* fv : t -> Id.t list *)
let fv e = remove_and_uniq S.empty (fv_o e)

let rec fv_exp2 = function
  | Nop | In | GetHp | Li (_) | FLi (_) | SetL (_) | Comment (_) | Restore (_) -> false, []
  | Mr (x) | FMr (x) | Save (x, _) | Sqrt (x) | ToFloat(x) | ToInt(x) | ToArray(x) | Out (x) | SetHp (x) -> false, [x]
  | Add (x, y') | Sub (x, y') | Xor (x, y') | Or (x, y') | And (x, y') | Sll (x, y') | Srl (x, y') |  Lfd (x, y') | Ldw (x, y') -> 
      false, x :: fv_id_or_imm y'
  | FAdd (x, y) | FMul (x, y) | FDiv (x, y) ->
      false, [x; y]
  | Stw (x, y, z') | Stfd (x, y, z') -> false, x :: y :: fv_id_or_imm z'
  | IfEq (x, y', e1, e2) | IfLE (x, y', e1, e2) | IfGE (x, y', e1, e2) ->
     let c1, rs1 = fv_o2 e1 in
     let c2, rs2 = fv_o2 e2 in
     c1 && c2, x :: fv_id_or_imm y' @ remove_and_uniq S.empty (rs1 @ rs2)
  | IfFEq (x, y, e1, e2) | IfFLE (x, y, e1, e2) ->
     let c1, rs1 = fv_o2 e1 in
     let c2, rs2 = fv_o2 e2 in
     c1 && c2, x :: y :: remove_and_uniq S.empty (rs1 @ rs2)
  | CallCls (x, ys, zs) -> true, x :: ys @ zs
  | CallDir (_, ys, zs) -> true, ys @ zs
and fv_o2 = function 
  | Ans (exp) -> fv_exp2 exp
  | Let ((x, t), exp, e) ->
     let c1, rs1 = fv_exp2 exp in
     if c1 then true, rs1 else
       let c2, rs2 = fv_o2 e in
       c2, rs1 @ remove_and_uniq (S.singleton x) rs2

(* fv2 : t -> Id.t list *)
let fv2 e = let c, rs = fv_o2 e in remove_and_uniq S.empty rs


let fv_id_or_imm3 func crs = function V(x) -> func x crs | _ -> crs

let rec fv_exp3 func all crs = function
  | Nop | In | GetHp | Li (_) | FLi (_) | SetL (_) | Comment (_) | Restore (_) -> crs
  | Mr (x) | FMr (x) | Save (x, _) | Sqrt (x) | ToFloat(x) | ToInt(x) | ToArray(x) | Out (x) | SetHp (x) -> func x crs
  | Add (x, y') | Sub (x, y') | Xor (x, y') | Or (x, y') | And (x, y') | Sll (x, y') | Srl (x, y') |  Lfd (x, y') | Ldw (x, y') -> func x (fv_id_or_imm3 func crs y')
  | FAdd (x, y) | FMul (x, y) | FDiv (x, y) ->
     func x (func y crs)
  | Stw (x, y, z') | Stfd (x, y, z') -> func x (func y (fv_id_or_imm3 func crs z'))
  | IfEq (x, y', e1, e2) | IfLE (x, y', e1, e2) | IfGE (x, y', e1, e2) ->
     let crs = fv_o3 func all crs e1 in
     let crs =
       if S.cardinal all = List.length crs then
	 crs
       else
	 fv_o3 func all crs e2
     in
     let crs = remove_and_uniq S.empty crs in
     func x (fv_id_or_imm3 func crs y')
  | IfFEq (x, y, e1, e2) | IfFLE (x, y, e1, e2) ->
     let crs = fv_o3 func all crs e1 in
     let crs =
       if S.cardinal all = List.length crs then
	 crs
       else
	 fv_o3 func all crs e2
     in
     let crs = remove_and_uniq S.empty crs in
     func x (func y crs)
  | CallCls (x, ys, zs) ->
     List.fold_left
       (fun crs y -> func y crs)
       crs
       (x :: ys @ zs)
  | CallDir (_, ys, zs) ->
     List.fold_left
       (fun crs y -> func y crs)
       crs
       (ys @ zs)
and fv_o3 func all crs = function 
  | Ans (exp) -> fv_exp3 func all crs exp
  | Let ((x, t), exp, e) ->
     let crs = remove_and_uniq S.empty (fv_exp3 func all crs exp) in
     if S.cardinal all = List.length crs then
       crs
     else
       fv_o3 func all crs e
				
(* fv3 : t -> (fun Id.t -> Id.t') -> Id.t list -> Id.t list *)
let fv3 e func all =
  let rec conv_all = function
    | [] -> S.empty
    | r::rs -> S.add r (conv_all rs)
  in
  let all = conv_all all in
  let func y crs = match func(y) with
    | None -> crs
    | Some(r) ->
       if S.mem r all && not (List.mem r crs) then
	 r::crs
       else
	 crs
  in
  remove_and_uniq S.empty (fv_o3 func all [] e)
				
				
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
