type id_or_imm = V of Id.t | C of int
type l_or_imm = L of Id.l | C of int
type t = 
  | Ans of exp
  | Let of (Id.t * Type.t) list * exp * t
and exp = 
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
  (* virtual instructions *)
  | Cmp of int * Id.t * id_or_imm
  | FCmp of int * Id.t * Id.t
  | Cmpa of int * Id.t * id_or_imm * Id.t
  | FCmpa of int * Id.t * Id.t * Id.t
  | If of int * Id.t * Id.t * t * t
  | FIf of int * Id.t * Id.t * t * t
  | IfThen of Id.t * t * Id.t list
  (* closure address, integer arguments, and float arguments *)
  | CallCls of Id.t * Id.t list
  | CallDir of Id.l * Id.t list
  | While of Id.l * Id.t list * t
  | Continue of Id.l * Id.t list
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of Id.t (* スタック変数から値を復元 *)
type fundef =
    { name : Id.l; args : Id.t list; body : t; ret : Type.t }
type prog = Prog of (Id.l * int) list * Id.l list * fundef list * t

val negcond : int -> int
val swapcond : int -> int
    
val seq : exp * t -> t (* shorthand of Let for unit *)

val regs : Id.t array
val allregs : Id.t list
val reg_cl : Id.t
val reg_sw : Id.t
val reg_hp : Id.t
val reg_sp : Id.t
val reg_tmp : Id.t
val reg_imm : Id.t
val reg_lr : Id.t
val reg_zero : Id.t
val reg_m1 : Id.t
val heap_start : int
val stack_start : int
val is_reg : Id.t -> bool
  
val rm_t : (Id.t * Type.t) list -> Id.t list
val rm_x : (Id.t * Type.t) list -> Type.t list
val unify_xt : Id.t list ->  Type.t list -> (Id.t * Type.t) list
val fv_if : Id.t -> Id.t -> Id.t list -> Id.t list -> Id.t list
val fv_ifthen : Id.t -> Id.t list -> Id.t list -> Id.t list
val fv_while : Id.t list -> Id.t list -> Id.t list
val fv_let : Id.t list -> Id.t list -> Id.t list -> Id.t list
val fv_exp : exp -> Id.t list
val fv_o : t -> Id.t list
val fv : t -> Id.t list
val rm_t_s : (Id.t * Type.t) list -> S.t
val fvs_if : Id.t -> Id.t -> S.t -> S.t -> S.t
val fvs_ifthen : Id.t -> S.t  -> Id.t list -> S.t
  val fvs_while : Id.t list -> S.t -> S.t
val fvs_let : Id.t list -> S.t -> S.t -> S.t
val fvs_exp : exp -> S.t
val fvs : t -> S.t
val concatfvs : t -> (Id.t * Type.t) list -> S.t -> S.t
val lconcatfvs : t -> (Id.t * Type.t) list -> S.t -> S.t
val concatfvs' : t -> (Id.t * Type.t) list -> S.t -> S.t -> S.t * S.t
val effect : exp -> bool
val concat : t -> (Id.t * Type.t) list -> t -> t
val concatfv : t -> (Id.t * Type.t) list -> Id.t list -> Id.t list

val align : int -> int

type dest = Tail | NonTail of Id.t list
val show : fundef list -> t -> unit
