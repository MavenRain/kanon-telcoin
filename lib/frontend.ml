module K = Kanon_kernel
module E = Kanon_kernel.Eterm
module S = Kanon_surface.Syntax
module Tok = Kanon_surface.Token

type error =
  | Kernel of K.Error.t
  | Unsupported of string

let error_to_string (error : error) : string =
  match error with
  | Kernel problem -> K.Error.to_string problem
  | Unsupported message -> "unsupported: " ^ message

let ( let* ) = Result.bind

let kernel result = Result.map_error (fun error -> Kernel error) result
let unsupported message = Error (Unsupported message)

let max_source_bytes = 65536
let max_nodes = 4096
let max_depth = 128
let word_limit = Z.shift_left Z.one 256
let within_word value = Z.sign value >= 0 && Z.compare value word_limit < 0

type lowered = {
  expression : Contract_ir.expr;
  nodes : int;
  depth : int;
}

let bounded expression nodes depth =
  if nodes > max_nodes then unsupported "the expanded transition exceeds 4096 nodes"
  else if depth > max_depth then unsupported "the transition exceeds depth 128"
  else Ok { expression; nodes; depth }

let validate_literal value =
  if within_word value then Ok ()
  else unsupported "a Nat literal is outside the uint256 range"

let constant value =
  let* () = validate_literal value in
  bounded (Contract_ir.Const value) 1 1

let nat_repr (representation : E.repr) : bool =
  match representation with
  | E.RUnion (E.Tid name) -> String.equal name "nat"
  | E.RI31 | E.RStruct _ | E.RFunc _ | E.RThunk _ -> false

let builtin_names = K.Prim.nat_name :: List.map K.Prim.name K.Prim.catalog

(* Restrict tokens and syntax before elaboration can evaluate a closed let.
   Inputs that pass this guard still pass through the actual kernel checker. *)
let lexical_limits source =
  let* _state =
    String.fold_left
      (fun result character ->
        let* comment, dash, digits, identifier = result in
        match () with
        | () when Char.equal character '\n' -> Ok (false, false, 0, 0)
        | () when comment || (dash && Char.equal character '-') -> Ok (true, false, 0, 0)
        | () ->
            let digits = if Kanon_surface.Lexer.is_digit character then digits + 1 else 0 in
            let identifier =
              if Kanon_surface.Lexer.is_ident_char character then identifier + 1 else 0
            in
            if digits > 78 then unsupported "a numeric lexeme exceeds 78 digits"
            else if identifier > 256 then unsupported "an identifier exceeds 256 characters"
            else Ok (false, Char.equal character '-', digits, identifier))
      (Ok (false, false, 0, 0)) source
  in
  Ok ()

let token_limits tokens =
  let* _counts =
    List.fold_left
      (fun result token ->
        let* count, parentheses, recursive_syntax = result in
        if count >= max_nodes then unsupported "the source exceeds 4096 tokens"
        else
          let* parentheses, recursive_syntax =
            match token.Tok.kind with
            | Tok.LParen -> Ok (parentheses + 1, recursive_syntax)
            | Tok.RParen -> Ok (Int.max 0 (parentheses - 1), recursive_syntax)
            | Tok.KLet | Tok.KFun | Tok.Arrow -> Ok (parentheses, recursive_syntax + 1)
            | Tok.Nat value ->
                let* () = validate_literal value in
                Ok (parentheses, recursive_syntax)
            | Tok.Colon | Tok.ColonEq | Tok.DArrow | Tok.KDef | Tok.KIn
            | Tok.KNatAdd | Tok.KNatSub | Tok.KNatMul | Tok.Ident _ | Tok.Eof ->
                Ok (parentheses, recursive_syntax)
            | Tok.KAxiom -> unsupported "user axiom"
            | Tok.KRec -> unsupported "recursive definition"
            | Tok.KMu | Tok.KNu | Tok.KAnd -> unsupported "family or mutual declaration"
            | Tok.Star | Tok.Comma | Tok.Dot | Tok.Dot1 | Tok.Dot2 | Tok.Pipe
            | Tok.Unit | Tok.KInj | Tok.KOf | Tok.KCase | Tok.KAs | Tok.KReturn
            | Tok.KWith | Tok.KTuple | Tok.KSum | Tok.KProd | Tok.KAbsurd
            | Tok.KProp | Tok.KType | Tok.KAuto | Tok.KNatEq | Tok.KNatLt ->
                unsupported ("surface form " ^ Tok.describe token.Tok.kind)
          in
          if parentheses > max_depth then unsupported "parenthesis nesting exceeds 128"
          else if recursive_syntax > max_depth then
            unsupported "the source exceeds 128 function, arrow and let tokens"
          else Ok (count + 1, parentheses, recursive_syntax))
      (Ok (0, 0, 0)) tokens
  in
  Ok ()

let bare_nat term =
  match term with
  | S.SVar name -> String.equal name K.Prim.nat_name
  | S.SNat _ | S.SProp | S.SType _ | S.SPrim _ | S.SUnit | S.SAuto
  | S.SPair _ | S.STuple _ | S.SSum _ | S.SProd _ | S.SProj _ | S.SInj _
  | S.SAbsurd _ | S.SApp _ | S.SFun _ | S.SArrow _ | S.SStar _ | S.SLet _
  | S.SAnn _ | S.SCase _ -> false

let require_nat term =
  if bare_nat term then Ok () else unsupported "a type annotation other than bare Nat"

type preflight_size = { pf_nodes : int; pf_depth : int; pf_bits : int }

let preflight_size nodes depth bits =
  match () with
  | () when nodes > max_nodes -> unsupported "expanded arithmetic exceeds 4096 nodes"
  | () when depth > max_depth -> unsupported "expanded arithmetic exceeds depth 128"
  | () when bits > 16384 -> unsupported "arithmetic may exceed 16384 bits"
  | () -> Ok { pf_nodes = nodes; pf_depth = depth; pf_bits = bits }

let preflight_binary primitive left right =
  let* bits =
    match primitive with
    | S.PAdd -> Ok (1 + Int.max left.pf_bits right.pf_bits)
    | S.PSub -> Ok left.pf_bits
    | S.PMul -> Ok (left.pf_bits + right.pf_bits)
    | S.PEq | S.PLt -> unsupported "a primitive outside Nat arithmetic"
  in
  preflight_size (1 + left.pf_nodes + right.pf_nodes)
    (1 + Int.max left.pf_depth right.pf_depth) bits

let rec preflight_expression depth remaining environment term =
  if depth > max_depth then unsupported "syntax exceeds depth 128"
  else if remaining <= 0 then unsupported "syntax exceeds 4096 nodes"
  else
    let remaining = remaining - 1 in
    match term with
    | S.SVar name ->
        let* size =
          Option.to_result ~none:(Unsupported ("global or unbound value " ^ name))
            (List.assoc_opt name environment)
        in
        Ok (size, remaining)
    | S.SNat value ->
        let* () = validate_literal value in
        let* size = preflight_size 1 1 (Int.max 1 (Z.numbits value)) in
        Ok (size, remaining)
    | S.SApp (S.SApp (S.SPrim primitive, left), right) ->
        let* left, remaining = preflight_expression (depth + 2) (remaining - 2) environment left in
        let* right, remaining = preflight_expression (depth + 1) remaining environment right in
        let* size = preflight_binary primitive left right in
        Ok (size, remaining)
    | S.SLet (name, annotation, value, body) ->
        let* () = require_nat annotation in
        let* value, remaining = preflight_expression (depth + 1) (remaining - 1) environment value in
        let* body, remaining = preflight_expression (depth + 1) remaining ((name, value) :: environment) body in
        let* size = preflight_size
          (3 + value.pf_nodes + body.pf_nodes)
          (Int.max (2 + value.pf_depth) (1 + body.pf_depth)) body.pf_bits in
        Ok (size, remaining)
    | S.SAnn (value, annotation) ->
        let* () = require_nat annotation in
        preflight_expression (depth + 1) (remaining - 1) environment value
    | S.SApp _ -> unsupported "an application other than saturated native Nat arithmetic"
    | S.SFun _ -> unsupported "a nested function or closure"
    | S.SProp | S.SType _ | S.SPrim _ | S.SUnit | S.SAuto | S.SPair _
    | S.STuple _ | S.SSum _ | S.SProd _ | S.SProj _ | S.SInj _ | S.SAbsurd _
    | S.SArrow _ | S.SStar _ | S.SCase _ ->
        unsupported "a body outside the Nat arithmetic fragment"

let preflight_body remaining signature body =
  match signature with
  | S.SVar _ ->
      let* () = require_nat signature in
      preflight_expression 1 (remaining - 1) [] body
  | S.SArrow (argument, result) ->
      let* () = require_nat argument.S.b_ty in
      let* () = require_nat result in
      (match body with
      | S.SFun ([ binder ], expression) ->
          let* () = require_nat binder.S.b_ty in
          let runtime_many quantity =
            match quantity with
            | K.Quantity.Many -> true
            | K.Quantity.Zero | K.Quantity.One -> false
          in
          if not (runtime_many argument.S.b_q && runtime_many binder.S.b_q) then
            unsupported "a transition binder must have unrestricted runtime quantity"
          else
            let* state = preflight_size 1 1 256 in
            preflight_expression 2 (remaining - 5) [ (binder.S.b_name, state) ] expression
      | S.SFun ([], _) | S.SFun (_ :: _ :: _, _) ->
          unsupported "a function without exactly one binder"
      | S.SVar _ | S.SNat _ | S.SProp | S.SType _ | S.SPrim _ | S.SUnit | S.SAuto
      | S.SPair _ | S.STuple _ | S.SSum _ | S.SProd _ | S.SProj _ | S.SInj _
      | S.SAbsurd _ | S.SApp _ | S.SArrow _ | S.SStar _ | S.SLet _ | S.SAnn _
      | S.SCase _ -> unsupported "a transition must be an explicit single-argument function")
  | S.SNat _ | S.SProp | S.SType _ | S.SPrim _ | S.SUnit | S.SAuto
  | S.SPair _ | S.STuple _ | S.SSum _ | S.SProd _ | S.SProj _ | S.SInj _
  | S.SAbsurd _ | S.SApp _ | S.SFun _ | S.SStar _ | S.SLet _ | S.SAnn _
  | S.SCase _ -> unsupported "a declaration type other than Nat or Nat -> Nat"

let preflight source =
  let scan () =
    let* () = lexical_limits source in
    let* tokens = kernel (Kanon_surface.Lexer.lex source) in
    let* () = token_limits tokens in
    let* declarations = kernel (Kanon_surface.Parser.parse_decls tokens []) in
    let* _state =
      List.fold_left
        (fun result declaration ->
          let* names, remaining = result in
          match declaration with
          | S.DDef (name, signature, body) ->
              if List.mem name builtin_names then unsupported ("a declaration redefines builtin " ^ name)
              else if List.mem name names then unsupported ("a declaration repeats name " ^ name)
              else
                let* _size, remaining = preflight_body (remaining - 1) signature body in
                Ok (name :: names, remaining)
          | S.DAxiom _ -> unsupported "user axiom"
          | S.DMu _ -> unsupported "family declaration"
          | S.DRec _ -> unsupported "recursive definition")
        (Ok ([], max_nodes)) declarations
    in
    Ok ()
  in
  Result.map_error
    (function
      | Kernel error -> Kernel error
      | Unsupported message -> Unsupported ("preflight: " ^ message))
    (scan ())

let check_declarations rows =
  let* _names =
    List.fold_left
      (fun result (name, declaration) ->
        let* names = result in
        if List.mem name builtin_names then
          unsupported ("a declaration redefines builtin " ^ name)
        else if List.mem name names then
          unsupported ("a declaration repeats name " ^ name)
        else
          match declaration with
          | K.Global.Def definition ->
              if definition.K.Global.partial || Option.is_some definition.K.Global.rec_arg then
                unsupported ("recursive or partial definition " ^ name)
              else Ok (name :: names)
          | K.Global.Axiom _ -> unsupported ("user axiom " ^ name)
          | K.Global.Prim _ -> unsupported ("user primitive " ^ name))
      (Ok []) rows
  in
  Ok ()

let check_signature budget globals entry =
  let signature =
    K.Rules.arrow K.Quantity.Many "state" K.Prim.nat_ty K.Prim.nat_ty
  in
  let* expected = kernel (K.Eval.eval globals [] signature) in
  kernel
    (K.Check.check
       (K.Check.make globals budget)
       K.Quantity.Many (K.Term.Global entry) expected)

let binary name left right =
  let* expression =
    match name with
    | "natAdd" -> Ok (Contract_ir.Add (left.expression, right.expression))
    | "natSub" -> Ok (Contract_ir.Sub (left.expression, right.expression))
    | "natMul" -> Ok (Contract_ir.Mul (left.expression, right.expression))
    | other -> unsupported ("call to " ^ other)
  in
  bounded expression (1 + left.nodes + right.nodes)
    (1 + Int.max left.depth right.depth)

let rec lower depth remaining environment term =
  if depth > max_depth then unsupported "the erased transition exceeds depth 128"
  else if remaining <= 0 then unsupported "the erased transition exceeds 4096 nodes"
  else
    let remaining = remaining - 1 in
    match term with
    | E.KVar index ->
        if index < 0 then unsupported "a negative erased variable index"
        else
          let* value =
            Option.to_result ~none:(Unsupported "an unbound erased variable")
              (List.nth_opt environment index)
          in
          Ok (value, remaining)
    | E.KLit (K.Literal.LInt value) ->
        let* value = constant value in
        Ok (value, remaining)
    | E.KLit (K.Literal.LString _) -> unsupported "a string literal"
    | E.KLet (_name, value, body) ->
        let* value, remaining = lower (depth + 1) remaining environment value in
        let* body, remaining = lower (depth + 1) remaining (value :: environment) body in
        (* Keep strict evaluation of an unused binding under checked arithmetic.
           Multiplying its value by zero sequences it without changing the result. *)
        let* zero = constant Z.zero in
        let* evaluated = binary "natMul" zero value in
        let* result = binary "natAdd" evaluated body in
        Ok (result, remaining)
    | E.KApp (head, arguments) | E.KTail (head, arguments) ->
        lower_call depth remaining environment head arguments
    | E.KGlobal _ -> unsupported "a global value or helper definition"
    | E.KErased -> unsupported "an erased value in the runtime transition"
    | E.KClos _ -> unsupported "a closure"
    | E.KStruct _ -> unsupported "a structure"
    | E.KProj _ -> unsupported "a structure projection"
    | E.KTag _ -> unsupported "a constructor tag"
    | E.KCase _ -> unsupported "case analysis"
    | E.KDelay _ -> unsupported "a delayed computation"
    | E.KForce _ -> unsupported "a forced computation"

and lower_call depth remaining environment head arguments =
  match head with
  | E.KGlobal name ->
      if remaining <= 0 then unsupported "the erased transition exceeds 4096 nodes"
      else
        (match arguments with
        | [ left; right ] ->
            let* left, remaining = lower (depth + 1) (remaining - 1) environment left in
            let* right, remaining = lower (depth + 1) remaining environment right in
            let* value = binary name left right in
            Ok (value, remaining)
        | [] | [ _ ] | _ :: _ :: _ :: _ ->
            unsupported "an arithmetic call without exactly two arguments")
  | E.KVar _ | E.KLit _ | E.KErased | E.KLet _ | E.KClos _
  | E.KApp _ | E.KTail _ | E.KStruct _ | E.KProj _ | E.KTag _
  | E.KCase _ | E.KDelay _ | E.KForce _ ->
      unsupported "an indirect function call"

let selected_function entry declarations =
  let* selected =
    List.fold_left
      (fun result declaration ->
        let* selected = result in
        match declaration with
        | E.KRec _ -> Ok selected
        | E.KFun (E.Fid name, parameters, result_type, body) ->
            if Option.is_some selected || not (String.equal name entry) then
              unsupported "a definition containing multiple or lifted functions"
            else
              (match parameters with
              | [ parameter ] ->
                  if nat_repr parameter && nat_repr result_type then Ok (Some body)
                  else unsupported "the erased signature is not Nat -> Nat"
              | [] | _ :: _ :: _ ->
                  unsupported "the erased transition does not have one parameter"))
      (Ok None) declarations
  in
  Option.to_result ~none:(Unsupported "the entry has no runtime function") selected

let checked_source ~entry source =
  if String.length source > max_source_bytes then
    unsupported "the source exceeds 65536 bytes"
  else
    let* () = preflight source in
    let polls = ref 0 in
    let budget = K.Budget.of_poll (fun () -> incr polls; !polls > 20000) in
    let* globals, rows =
      kernel (Kanon_surface.Elab.check_in ~budget K.Global.initial source)
    in
    let* () = check_declarations rows in
    let* _declaration =
      Option.to_result ~none:(Unsupported ("no source definition named " ^ entry))
        (List.assoc_opt entry rows)
    in
    let* () = check_signature budget globals entry in
    Ok (budget, globals, rows)

let eval_source ~entry ~state source =
  let* () =
    if within_word state then Ok () else unsupported "input state is outside uint256"
  in
  let* budget, globals, _rows = checked_source ~entry source in
  let application =
    K.Term.Out
      (K.Shape.SPi (K.Quantity.Many, "state", K.Prim.nat_ty),
       K.Term.APt (K.Quantity.Many, K.Term.Lit (K.Literal.LInt state)),
       K.Term.Global entry)
  in
  let* expected = kernel (K.Eval.eval globals [] K.Prim.nat_ty) in
  (* The kernel checks the synthetic application with the same 20000-poll budget
     that checked the source. Compilation spends the remainder of that budget on
     erasure instead. A source near the budget limit can be refused by one path
     and accepted by the other. Both refusals are resource refusals, not a
     semantic disagreement. *)
  let* () =
    kernel
      (K.Check.check (K.Check.make globals budget) K.Quantity.Many application expected)
  in
  let* value = kernel (K.Eval.eval globals [] application) in
  Option.to_result ~none:(Unsupported "source evaluation did not produce a Nat literal")
    (Option.bind (K.Value.as_lit value) K.Prim.as_nat)

let compile ~entry source =
  let* budget, globals, rows = checked_source ~entry source in
  let* erased = kernel (K.Erase.program ~budget globals rows) in
  let* selected =
    Option.to_result ~none:(Unsupported ("no erased entry named " ^ entry))
      (List.assoc_opt entry erased)
  in
  match selected with
  | K.Erase.Dropped -> unsupported "the selected definition is erased"
  | K.Erase.Postulate _ -> unsupported "the selected definition is a postulate"
  | K.Erase.Code declarations ->
      let* body = selected_function entry declarations in
      let state = { expression = Contract_ir.State; nodes = 1; depth = 1 } in
      let* value, _remaining = lower 1 max_nodes [ state ] body in
      Ok value.expression
