module K = Kanon_kernel
module F = Kanon_telcoin.Nat_fragment
module T = K.Term
module Q = K.Quantity
module Sh = K.Shape

let ( let* ) = Result.bind
let checks = ref 0
let check label condition =
  incr checks;
  if condition then Ok () else Error ("FAIL: " ^ label)
let accepted result = Result.map_error F.error_to_string result
let kernel result = Result.map_error K.Error.to_string result
let rejected label result =
  result |> Result.fold ~ok:(fun _ -> check label false) ~error:(fun _ -> check label true)

let eval_application globals name argument =
  let raw = T.Out (Sh.SPi (Q.Many, "n", F.nat_type), T.APt (Q.Many, argument), T.Global name) in
  let* _ty = kernel (K.Check.infer_term globals raw) in
  let* value = kernel (K.Eval.eval globals [] raw) in
  kernel (K.Eval.quote globals 0 value)

let run source =
  let* globals, rows = kernel (Kanon_surface.Elab.check_in K.Global.empty source) in
  let* () = check "one family, no axioms, builtin Nat, or primitives"
      (K.Global.StringMap.cardinal globals.K.Global.families = 1
       && List.for_all (fun (_name, entry) -> match entry with
         | K.Global.Def _ -> true | K.Global.Axiom _ | K.Global.Prim _ -> false) rows) in
  let* profile = accepted (F.profile globals) in
  let* () = check "actual source profile and generic guarded induction admitted" (String.length profile > 0) in
  let context = K.Check.make globals K.Budget.unlimited in
  let* signature = accepted (F.signature globals) in
  let* source_zero = accepted (F.adapt_term context F.zero) in
  let* source_one = accepted (F.adapt_term context (F.successor F.zero)) in
  let* () = check "source constructors map to distinct polynomial nodes"
      (source_zero = F.Zero && source_one = F.Succ F.Zero) in
  let* nat_value = kernel (K.Eval.eval globals [] F.nat_type) in
  let* bound_variable = accepted (F.adapt_term (K.Check.bind "n" Q.Many nat_value context) (T.Var 0)) in
  let* () = check "typed N context variable maps to DB0" (bound_variable = F.Variable 0) in
  let* () = rejected "well-scoped variable of wrong type"
      (F.adapt_term (K.Check.bind "T" Q.Many (K.Value.VUniv K.Level.one) context) (T.Var 0)) in
  let malformed_terms = [
    "wrong family payload", T.In (Sh.SMu ("Other", []), T.ACtor "zero", []);
    "wrong index payload", T.In (Sh.SMu ("N", [ F.zero ]), T.ACtor "zero", []);
    "wrong constructor address", T.In (F.shape, T.ALeg 0, []);
    "zero with a field", T.In (F.shape, T.ACtor "zero", [ F.zero ]);
    "succ without a field", T.In (F.shape, T.ACtor "succ", []);
    "negative DB index", T.Var (-1); "unbound DB index", T.Var 0 ] in
  let* () = List.fold_left (fun result (label, raw) -> let* () = result in
    rejected label (F.adapt_term context raw)) (Ok ()) malformed_terms in
  let wrong_field = { signature.F.succ_ctor with K.Positivity.c_args = [ (Q.Many, "n", T.Univ K.Level.one) ] } in
  let wrong_quantity = { signature.F.succ_ctor with K.Positivity.c_args = [ (Q.Zero, "n", F.nat_type) ] } in
  let malformed_families = [
    "same name, wrong field type", { signature.F.family with K.Positivity.f_ctors = [ signature.F.zero_ctor; wrong_field ] };
    "same name, erased field", { signature.F.family with K.Positivity.f_ctors = [ signature.F.zero_ctor; wrong_quantity ] };
    "same name, index telescope", { signature.F.family with K.Positivity.f_indices = [ (Q.Zero, "i", F.nat_type) ] } ] in
  let* () = List.fold_left (fun result (label, family) -> let* () = result in
    rejected label (F.validate_family family)) (Ok ()) malformed_families in
  let* case_context, _binders, view = accepted (F.definition_case globals "dependentCase") in
  let branches zero_branch succ_branch = [ T.ACtor "zero", zero_branch; T.ACtor "succ", succ_branch ] in
  let malformed_cases = [
    "case wrong index", { view.F.source with T.e_shape = Sh.SMu ("N", [ F.zero ]) };
    "motive index binder", { view.F.source with T.e_motive = Some { view.F.motive with T.m_idx = [ "i" ] } };
    "ill-scoped motive", { view.F.source with T.e_motive = Some { view.F.motive with T.m_body = T.Var 7 } };
    "motive wrong family", { view.F.source with T.e_motive = Some { view.F.motive with T.m_ind = Some "Other" } };
    "wrong scrutinee quantity", { view.F.source with T.e_scrut_q = Q.Many };
    "implicit IH binder", { view.F.source with T.e_branches = branches view.F.zero_branch
      { view.F.succ_branch with T.l_binders = [ Q.Many, "n"; Q.Many, "ih" ] } };
    "ill-scoped predecessor", { view.F.source with T.e_branches = branches view.F.zero_branch
      { view.F.succ_branch with T.l_body = T.Var 7 } };
    "malformed introduction hidden in branch", { view.F.source with T.e_branches = branches
      { view.F.zero_branch with T.l_body = T.In (Sh.SMu ("N", [ F.zero ]), T.ACtor "zero", []) } view.F.succ_branch } ] in
  let* () = List.fold_left (fun result (label, raw) -> let* () = result in
    rejected label (F.adapt_case case_context raw)) (Ok ()) malformed_cases in
  let* induction_context, _binders, induction = accepted (F.definition_case globals "induction") in
  let* application_with_domain =
    match induction.F.succ_branch.T.l_body with
    | T.Out (Sh.SPi (quantity, name, _domain), address, head) ->
        Ok (fun domain -> T.Out (Sh.SPi (quantity, name, domain), address, head))
    | T.Var _ | T.Univ _ | T.Lan _ | T.Ran _ | T.In _ | T.Elim _ | T.Sec _
    | T.Out _ | T.Let _ | T.Ann _ | T.Global _ | T.Lit _ | T.Auto -> Error "expected induction step application" in
  let application_case domain = { induction.F.source with T.e_branches = branches induction.F.zero_branch
    { induction.F.succ_branch with T.l_body = application_with_domain domain } } in
  let malformed_domains = [
    "ill-scoped SPi application annotation", T.Var 999;
    "ill-typed SPi application annotation", T.Out (Sh.SPi (Q.Many, "x", F.nat_type), T.APt (Q.Many, F.zero), F.zero);
    "wrong but well-typed SPi application annotation", T.Univ K.Level.one ] in
  let* () = List.fold_left (fun result (label, domain) -> let* () = result in
    rejected label (F.adapt_case induction_context (application_case domain))) (Ok ()) malformed_domains in
  let* observe_zero = eval_application globals "observe" F.zero in
  let* observe_one = eval_application globals "observe" (F.successor F.zero) in
  let* () = check "nonconstant observation separates zero from successor zero"
      (observe_zero = F.zero && observe_one = F.successor F.zero) in
  let* fiber_zero = eval_application globals "Fiber" F.zero in
  let* fiber_one = eval_application globals "Fiber" (F.successor F.zero) in
  let* () = check "dependent motive has genuinely different result types"
      (fiber_zero = F.nat_type && fiber_one = K.Rules.prod_ty [ F.nat_type; F.nat_type ]) in
  let pair value = T.Sec (Sh.SColl 2, [ K.Rules.leg_of value; K.Rules.leg_of value ]) in
  let* case_zero = eval_application globals "dependentCase" F.zero in
  let* case_one = eval_application globals "dependentCase" (F.successor F.zero) in
  let* () = check "dependent case beta at both constructors" (case_zero = F.zero && case_one = pair F.zero) in
  let* recursive_zero = eval_application globals "recursiveDependent" F.zero in
  let* recursive_two = eval_application globals "recursiveDependent" (F.successor (F.successor F.zero)) in
  let* () = check "guarded induction computes at nonconstant Fiber"
      (recursive_zero = F.zero && recursive_two = pair (F.successor F.zero)) in
  let two = F.successor (F.successor F.zero) in
  let* doubled_two = eval_application globals "double" two in
  let* () = check "recursive result contributes to both successor steps"
      (doubled_two = F.successor (F.successor two)) in
  let negative_sources = [
    "surface wrong motive index", "def bad : N -> N := fun (n : N) => case n as self in N i return N with | zero => zero | succ p => p";
    "surface unbound predecessor", "def bad : N -> N := fun (n : N) => case n as self in N return N with | zero => zero | succ p => missing";
    "surface wrong constructor", "def bad : N -> N := fun (n : N) => case n as self in N return N with | zero => zero | other p => p";
    "surface extra IH", "def bad : N -> N := fun (n : N) => case n as self in N return N with | zero => zero | succ p ih => p";
    "surface wrong predecessor quantity", "def bad : N -> N := fun (n : N) => case n as self in N return N with | zero => zero | succ 0 p => zero";
    "surface unguarded recursion", "def rec bad : N -> N := fun (n : N) => bad n" ] in
  let* () = List.fold_left (fun result (label, suffix) -> let* () = result in
    rejected label (Kanon_surface.Elab.check_in K.Global.empty (source ^ "\n" ^ suffix))) (Ok ()) negative_sources in
  Ok profile

let () =
  let source = In_channel.input_all stdin in
  run source |> Result.fold
    ~error:(fun problem -> prerr_endline problem; exit 1)
    ~ok:(fun profile ->
      if Array.exists (String.equal "--profile") Sys.argv then print_endline profile
      else Printf.printf "NatFragmentBridge: %d checks passed\n" !checks)
