module Ir = Kanon_telcoin.Contract_ir
module Evm = Kanon_telcoin.Evm
module Frontend = Kanon_telcoin.Frontend

let ( let* ) = Result.bind
let checks = ref 0

let check label condition =
  incr checks;
  if condition then Ok () else Error ("FAIL: " ^ label)

let const value = Ir.Const (Z.of_int value)

let emits label predicate expression =
  Evm.compile ~bound:Ir.max_word expression |> Result.fold
    ~ok:(fun artifact -> check label (predicate artifact))
    ~error:(fun problem -> check (label ^ ": " ^ problem) false)

let chars text = List.of_seq (String.to_seq text)

let rec starts_with needle haystack =
  match (needle, haystack) with
  | [], [] -> true
  | [], _ :: _ -> true
  | _ :: _, [] -> false
  | first :: needle_rest, head :: haystack_rest ->
      Char.equal first head && starts_with needle_rest haystack_rest

let rec contains needle haystack =
  starts_with needle haystack
  || (match haystack with
      | [] -> false
      | _head :: rest -> contains needle rest)

(* The emitted runtime holds this exact byte sequence. *)
let runtime_contains fragment artifact =
  contains (chars fragment) (chars artifact.Evm.runtime_hex)

let outcome expression =
  Evm.compile ~bound:Ir.max_word expression |> Result.map (fun _artifact -> ())

let source_for body =
  "def step : (state : Nat) -> Nat := fun (state : Nat) => " ^ body ^ "\n"

let run () =
  let open Ir in
  let deep_local =
    List.fold_right (fun value body -> Let (const value, body))
      (List.init 20 (fun index -> index + 1)) (Local 19)
  in
  let successful = [
    "shared RHS value", Let (Add (State, const 1), Mul (Local 0, Local 0)), 3, 16;
    "outer local under inner binder",
      Let (Add (State, const 3), Let (const 7, Mul (Local 1, Local 0))), 2, 35;
    "nested RHS restores enclosing scope",
      Let (const 11, Let (Let (const 3, Add (Local 0, Local 1)),
        Sub (Local 0, Local 1))), 0, 3;
    "sibling scopes are independent",
      Add (Let (const 3, Local 0), Let (const 7, Local 0)), 0, 10;
    "twenty nested locals", deep_local, 0, 1;
  ] in
  let* () = List.fold_left (fun result (label, expression, state, expected) ->
    let* () = result in
    let* () = check (label ^ " evaluates")
      (eval (Z.of_int state) expression = Ok (Z.of_int expected)) in
    emits (label ^ " compiles") (fun _artifact -> true) expression) (Ok ()) successful in
  let overflow = Add (Const max_word, const 1) in
  let strict = [
    "unused RHS overflow", Let (overflow, const 0);
    "unused overflow nested inside RHS",
      Let (Let (overflow, const 7), Add (Local 0, Local 0));
  ] in
  let* () = List.fold_left (fun result (label, expression) ->
    let* () = result in
    let* () = check (label ^ " is strict")
      (eval Z.zero expression = Error Intermediate_overflow) in
    emits (label ^ " compiles") (fun _artifact -> true) expression) (Ok ()) strict in
  let malformed = [
    "negative local", Local (-1), -1, "EVM local index is negative";
    "unbound local", Local 0, 0, "EVM local index is unbound";
    "binding is absent in its own RHS", Let (Local 0, const 1), 0,
      "EVM local index is unbound";
    "binding does not escape to a sibling", Add (Let (const 1, Local 0), Local 0), 0,
      "EVM local index is unbound";
    "index past enclosing binder", Let (const 1, Local 1), 1,
      "EVM local index is unbound";
    "negative local beneath binder", Let (const 1, Local (-1)), -1,
      "EVM local index is negative";
  ] in
  let* () = List.fold_left (fun result (label, expression, index, diagnostic) ->
    let* () = result in
    let* () = check (label ^ " fails evaluation explicitly")
      (eval Z.zero expression = Error (Unbound_local index)) in
    check (label ^ " fails emission explicitly")
      (Evm.compile ~bound:max_word expression = Error diagnostic)) (Ok ()) malformed in
  let* () = check "RHS failure precedes body failure"
    (eval Z.zero (Let (overflow, Local 1)) = Error Intermediate_overflow) in
  let nested count =
    List.fold_left (fun body _index -> Let (const 1, body)) (const 1)
      (List.init count Fun.id) in
  (* Every child of a balanced Let tree holds an odd count, so the total is exact. *)
  let rec balanced size =
    if size <= 1 then const 1
    else
      let left = (size / 2 / 2 * 2) + 1 in
      Let (balanced left, balanced (size - 1 - left)) in
  let limits = [
    "257 nested lets exceed the emitter depth limit", nested 257,
      Error "EVM expression exceeds nesting depth 256";
    "256 nested lets are emitted", nested 256, Ok ();
    "1025 nodes exceed the emitter node limit", balanced 1025,
      Error "EVM expression exceeds 1024 nodes";
    "1023 nodes are emitted", balanced 1023, Ok ();
  ] in
  let* () = List.fold_left (fun result (label, expression, expected) ->
    let* () = result in
    check label (outcome expression = expected)) (Ok ()) limits in
  let* shared = Evm.compile ~bound:max_word
    (Let (Add (State, const 1), Mul (Local 0, Local 0))) in
  let* repeated = Evm.compile ~bound:max_word
    (Mul (Add (State, const 1), Add (State, const 1))) in
  let* () = check "sharing emits less runtime code than repetition"
    (String.length shared.Evm.runtime_hex
     < String.length repeated.Evm.runtime_hex) in
  let* stored = Evm.compile ~bound:max_word (Let (const 5, Local 0)) in
  let* () = check "a let value is stored and loaded at a nonzero memory slot"
    (runtime_contains "6005602052602051" stored) in
  let lowered = [
    "shared source lowers once",
      "let x : Nat := natAdd state 1 in natMul x x",
      Let (Add (State, const 1), Mul (Local 0, Local 0));
    "shadowed RHS preserves outer local",
      "let x : Nat := natAdd state 4 in "
      ^ "let y : Nat := (let x : Nat := natAdd x 1 in natMul x 2) in natSub y x",
      Let (Add (State, const 4),
        Let (Let (Add (Local 0, const 1), Mul (Local 0, const 2)),
          Sub (Local 0, Local 1)));
    "inner operand restores surrounding scope",
      "let x : Nat := natAdd state 2 in "
      ^ "natSub (let y : Nat := natMul x 3 in natAdd y x) x",
      Let (Add (State, const 2),
        Sub (Let (Mul (Local 0, const 3), Add (Local 0, Local 1)), Local 0));
  ] in
  List.fold_left (fun result (label, source, expected) ->
    let* () = result in
    let* actual = Frontend.compile ~entry:"step" (source_for source)
      |> Result.map_error Frontend.error_to_string in
    check label (actual = expected)) (Ok ()) lowered

let () =
  run () |> Result.fold
    ~error:(fun problem -> prerr_endline problem; exit 1)
    ~ok:(fun () -> Printf.printf "ContractIr: %d checks passed\n" !checks)
