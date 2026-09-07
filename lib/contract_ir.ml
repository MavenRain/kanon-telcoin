(** A deliberately small runtime fragment, checked before lowering. *)
type expr =
  | State
  | Const of Z.t
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr

let max_word : Z.t = Z.pred (Z.shift_left Z.one 256)

type eval_error = Intermediate_overflow

(** Bounded execution of natural arithmetic. Every intermediate must fit a word.
    Subtraction retains natural-number saturation at zero. *)
let rec eval (state : Z.t) (expr : expr) : (Z.t, eval_error) result =
  let checked n =
    if Z.sign n < 0 || Z.gt n max_word then Error Intermediate_overflow
    else Ok n
  in
  let both op a b =
    Result.bind (eval state a) (fun x ->
        Result.bind (eval state b) (fun y -> checked (op x y)))
  in
  match expr with
  | State -> checked state
  | Const n -> checked n
  | Add (a, b) -> both Z.add a b
  | Sub (a, b) -> both (fun x y -> Z.max Z.zero (Z.sub x y)) a b
  | Mul (a, b) -> both Z.mul a b
