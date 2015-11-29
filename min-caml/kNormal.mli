type t =
  | Unit
  | Int of int
  | Float of float
  | Array of int
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
  | FAM of Id.t * Id.t * Id.t
  | FAbs of Id.t
  | Sqrt of Id.t
  | If of int * Id.t * Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of Id.t * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.t
  | ToFloat of Id.t
  | ToInt of Id.t
  | ToArray of Id.t
  | In of Id.t
  | Out of Id.t
  | Count
  | ShowExec
  | SetCurExec
  | GetExecDiff
  | GetHp of Id.t
  | SetHp of Id.t
  | ExtFunApp of Id.t * Id.t list
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

val size : t -> int
val fv : t -> S.t
val fv_let : Id.t -> S.t -> S.t -> S.t
val fv_if : Id.t -> Id.t -> S.t -> S.t -> S.t
val fv_func : Id.t -> (Id.t * Type.t) list -> S.t -> S.t
val fv_letrec : Id.t -> (Id.t * Type.t) list -> S.t -> S.t -> S.t
val fv_lettuple : (Id.t * Type.t) list -> Id.t -> S.t -> S.t
val f : Syntax.t -> t
