(** A deliberately small runtime fragment, checked before lowering. *)
type expr =
  | State
  | Const of Z.t
  (* Local 0 names the innermost let binding. A let evaluates its value once
     before evaluating its body in the extended scope. *)
  | Local of int
  | Let of expr * expr
  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr

let max_word : Z.t = Z.pred (Z.shift_left Z.one 256)

type eval_error =
  | Intermediate_overflow
  | Unbound_local of int

(** Bounded execution of natural arithmetic. Every intermediate must fit a word.
    Subtraction retains natural-number saturation at zero. *)
let eval (state : Z.t) (expr : expr) : (Z.t, eval_error) result =
  let checked n =
    if Z.sign n < 0 || Z.gt n max_word then Error Intermediate_overflow
    else Ok n
  in
  let rec evaluate environment expression =
    let both op a b =
      Result.bind (evaluate environment a) (fun x ->
          Result.bind (evaluate environment b) (fun y -> checked (op x y)))
    in
    match expression with
    | State -> checked state
    | Const n -> checked n
    | Local index ->
        if index < 0 then Error (Unbound_local index)
        else
          Option.to_result ~none:(Unbound_local index)
            (List.nth_opt environment index)
    | Let (value, body) ->
        Result.bind (evaluate environment value) (fun value ->
            evaluate (value :: environment) body)
    | Add (a, b) -> both Z.add a b
    | Sub (a, b) -> both (fun x y -> Z.max Z.zero (Z.sub x y)) a b
    | Mul (a, b) -> both Z.mul a b
  in
  evaluate [] expr
