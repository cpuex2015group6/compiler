type closure = { entry : Id.l; actual_fv : Id.t list }
type t =
  | Unit
  | Int of int
  | Float of float
  | Neg of Id.t
  | Add of Id.t * Id.t
  | Sub of Id.t * Id.t
  | Xor of Id.t * Id.t
  | Or of Id.t * Id.t
  | And of Id.t * Id.t
  | Sll of Id.t * Id.t
  | Srl of Id.t * Id.t
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | FAbA of Id.t * Id.t
  | FAM of Id.t * Id.t * Id.t
  | FAbs of Id.t
  | Sqrt of Id.t
  | I2F of Id.t
  | F2I of Id.t
  | I2IA of Id.t
  | I2FA of Id.t
  | A2I of Id.t
  | In
  | Out of Id.t
  | GetHp
  | SetHp of Id.t
  | If of int * Id.t * Id.t * t * t
  | While of Id.l * (Id.t * Type.t) list * Id.t list * t
  | Continue of Id.l * (Id.t * Type.t) list  * Id.t list
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | MakeCls of (Id.t * Type.t) * closure * t
  | AppCls of Id.t * Id.t list
  | AppDir of Id.l * Id.t list
  | Tuple of Id.t list
  | GetTuple of Id.t * int
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.l
type fundef = { name : Id.l * Type.t;
		args : (Id.t * Type.t) list;
		formal_fv : (Id.t * Type.t) list;
		body : t }
type prog = Prog of fundef list * t

val fv : t -> S.t
val f : KNormal.t -> prog
