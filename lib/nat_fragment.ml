(* A deliberately narrow adapter for the foundation experiment. The EVM
   frontend does not call this module. Kernel admission is checked first. *)
module K = Kanon_kernel
module T = K.Term
module Q = K.Quantity
module Sh = K.Shape

type error = Kernel of K.Error.t | Outside_fragment of string

let error_to_string = function
  | Kernel problem -> K.Error.to_string problem
  | Outside_fragment message -> "Nat fragment: " ^ message

let ( let* ) = Result.bind
let kernel result = Result.map_error (fun problem -> Kernel problem) result
let require condition message =
  if condition then Ok () else Error (Outside_fragment message)

let missing message = Outside_fragment message
let shape = Sh.SMu ("N", [])
let nat_type = T.Lan (shape, T.Sec (Sh.SColl 0, []))
let zero = T.In (shape, T.ACtor "zero", [])
let successor predecessor = T.In (shape, T.ACtor "succ", [ predecessor ])

(* Scope includes annotation payloads that the runtime-oriented rule packs
   may not inspect. A former's SPi diagram binds one point; branch bodies
   bind their declared fields, and an explicit motive binds indices then self. *)
let rec well_scoped scope raw =
  let all terms = List.fold_left (fun result term ->
    let* () = result in well_scoped scope term) (Ok ()) terms in
  let shape_scope source_shape = all (Sh.payload source_shape) in
  let address_scope address =
    match address with
    | T.APt (_quantity, argument) -> well_scoped scope argument
    | T.ALeg _ | T.ACtor _ -> Ok ()
  in
  let leg_scope leg = well_scoped (scope + List.length leg.T.l_binders) leg.T.l_body in
  match raw with
  | T.Var index -> require (index >= 0 && index < scope) "ill-scoped variable or annotation payload"
  | T.Univ _ | T.Global _ | T.Lit _ | T.Auto -> Ok ()
  | T.Lan (source_shape, diagram) | T.Ran (source_shape, diagram) ->
      let* () = shape_scope source_shape in
      let extra = match source_shape with
        | Sh.SPi _ -> 1
        | Sh.SColl _ | Sh.SMu _ | Sh.SPar _ | Sh.SNu _ -> 0 in
      well_scoped (scope + extra) diagram
  | T.In (source_shape, address, arguments) ->
      let* () = shape_scope source_shape in
      let* () = address_scope address in
      all arguments
  | T.Sec (source_shape, legs) ->
      let* () = shape_scope source_shape in
      List.fold_left (fun result leg -> let* () = result in leg_scope leg) (Ok ()) legs
  | T.Out (source_shape, address, head) ->
      let* () = shape_scope source_shape in
      let* () = address_scope address in
      well_scoped scope head
  | T.Elim source ->
      let* () = shape_scope source.T.e_shape in
      let* () = well_scoped scope source.T.e_scrut in
      let* () = Option.fold ~none:(Ok ()) ~some:(fun motive ->
        well_scoped (scope + List.length motive.T.m_idx + 1) motive.T.m_body) source.T.e_motive in
      List.fold_left (fun result (address, leg) ->
        let* () = result in
        let* () = address_scope address in
        leg_scope leg) (Ok ()) source.T.e_branches
  | T.Let (_name, ty, value, body) ->
      let* () = all [ ty; value ] in
      well_scoped (scope + 1) body
  | T.Ann (value, ty) -> all [ value; ty ]

(* The pinned checker does not use every introduction shape payload.
   Check them syntactically throughout the accepted source as well. *)
let rec validate_shapes raw =
  match raw with
  | T.Var _ | T.Univ _ | T.Global _ | T.Lit _ | T.Auto -> Ok ()
  | T.Lan (source_shape, diagram) ->
      let* () = validate_shape source_shape in
      let* () =
        match source_shape with
        | Sh.SMu _ -> require (diagram = T.Sec (Sh.SColl 0, [])) "N has no parameter diagram"
        | Sh.SPi _ | Sh.SColl _ | Sh.SPar _ | Sh.SNu _ -> Ok ()
      in
      validate_shapes diagram
  | T.Ran (source_shape, diagram) ->
      let* () = validate_shape source_shape in
      let* () =
        match source_shape with
        | Sh.SMu _ -> Error (missing "right SMu is outside the fragment")
        | Sh.SPi _ | Sh.SColl _ | Sh.SPar _ | Sh.SNu _ -> Ok ()
      in
      validate_shapes diagram
  | T.In (source_shape, address, arguments) ->
      let* () = validate_shape source_shape in
      let* () =
        match source_shape, address, arguments with
        | Sh.SMu _, T.ACtor "zero", [] -> Ok ()
        | Sh.SMu _, T.ACtor "succ", [ _ ] -> Ok ()
        | Sh.SMu _, (T.APt _ | T.ALeg _ | T.ACtor _), _ ->
            Error (missing "N introduction has a wrong constructor or fields")
        | (Sh.SPi _ | Sh.SColl _ | Sh.SPar _ | Sh.SNu _), _, _ -> Ok ()
      in
      let* () = validate_address address in
      validate_terms arguments
  | T.Elim source ->
      let* () = validate_shape source.T.e_shape in
      let* () = validate_shapes source.T.e_scrut in
      let* () = Option.fold ~none:(Ok ())
          ~some:(fun motive -> validate_shapes motive.T.m_body) source.T.e_motive in
      List.fold_left (fun result (address, leg) ->
        let* () = result in
        let* () = validate_address address in
        validate_shapes leg.T.l_body) (Ok ()) source.T.e_branches
  | T.Sec (source_shape, legs) ->
      let* () = validate_shape source_shape in
      validate_terms (List.map (fun leg -> leg.T.l_body) legs)
  | T.Out (source_shape, address, head) ->
      let* () = validate_shape source_shape in
      let* () = validate_address address in
      validate_shapes head
  | T.Let (_name, ty, value, body) -> validate_terms [ ty; value; body ]
  | T.Ann (value, ty) -> validate_terms [ value; ty ]

and validate_shape source_shape =
  match source_shape with
  | Sh.SMu _ -> require (source_shape = shape) "SMu payload must be N without indices"
  | Sh.SPi (_quantity, _name, domain) -> validate_shapes domain
  | Sh.SColl width -> require (width >= 0) "negative collection width"
  | Sh.SPar _ | Sh.SNu _ -> Error (missing "shape outside the fragment")

and validate_address address =
  match address with
  | T.APt (_quantity, argument) -> validate_shapes argument
  | T.ALeg _ | T.ACtor _ -> Ok ()

and validate_terms terms =
  List.fold_left (fun result term -> let* () = result in validate_shapes term) (Ok ()) terms

type signature = { family : K.Positivity.family; zero_ctor : K.Positivity.ctor;
                   succ_ctor : K.Positivity.ctor }

let validate_family family =
  let* () = require (String.equal family.K.Positivity.f_name "N") "family must be N" in
  let* () = require (family.K.Positivity.f_params = []) "parameters are outside the fragment" in
  let* () = require (family.K.Positivity.f_indices = []) "indices are outside the fragment" in
  let* () = require (K.Level.equal family.K.Positivity.f_level K.Level.one) "N must inhabit Type0" in
  let* () = require family.K.Positivity.f_positive "family positivity must be checked" in
  let* () = require
      (family.K.Positivity.f_status = K.Positivity.Complete [ "zero"; "succ" ])
      "constructor status must be complete in zero, succ order" in
  match family.K.Positivity.f_ctors with
  | [ zero_ctor; succ_ctor ] ->
      let* () = require
          (String.equal zero_ctor.K.Positivity.c_name "zero"
           && zero_ctor.K.Positivity.c_args = []
           && zero_ctor.K.Positivity.c_res_idx = []
           && zero_ctor.K.Positivity.c_full_arity = 0
           && not zero_ctor.K.Positivity.c_self_rec)
          "zero must be nullary, nonrecursive, and unindexed" in
      let* () = require
          (String.equal succ_ctor.K.Positivity.c_name "succ"
           && succ_ctor.K.Positivity.c_res_idx = []
           && succ_ctor.K.Positivity.c_full_arity = 1
           && succ_ctor.K.Positivity.c_self_rec)
          "succ must have one recursive field and no result indices" in
      let* () =
        match succ_ctor.K.Positivity.c_args with
        | [ (Q.Many, _name, ty) ] -> require (ty = nat_type) "successor field must be exactly N"
        | [] | [ (Q.Zero, _, _) ] | [ (Q.One, _, _) ] | _ :: _ :: _ ->
            Error (missing "successor requires one unrestricted field")
      in
      Ok { family; zero_ctor; succ_ctor }
  | [] | [ _ ] | _ :: _ :: _ :: _ -> Error (missing "N requires exactly zero and succ")

let signature globals =
  let* family = K.Global.find_family "N" globals
    |> Option.to_result ~none:(missing "no checked family N") in
  validate_family family

(* These constructors map to SourceTerm in NatFragmentBridge. An index is
   accepted only when the supplied typed kernel context gives it type N. *)
type term = Variable of int | Zero | Succ of term

let rec decode ~scope raw =
  match raw with
  | T.Var index ->
      let* () = require (index >= 0 && index < scope) "ill-scoped de Bruijn index" in
      Ok (Variable index)
  | T.In (source_shape, address, arguments) ->
      let* () = require (source_shape = shape) "constructor has a wrong family or index" in
      (match address, arguments with
      | T.ACtor "zero", [] -> Ok Zero
      | T.ACtor "succ", [ predecessor ] ->
          Result.map (fun value -> Succ value) (decode ~scope predecessor)
      | (T.APt _ | T.ALeg _ | T.ACtor _), _ ->
          Error (missing "constructor address or fields do not match 1+X"))
  | T.Univ _ | T.Lan _ | T.Ran _ | T.Elim _ | T.Sec _ | T.Out _
  | T.Let _ | T.Ann _ | T.Global _ | T.Lit _ | T.Auto ->
      Error (missing "term is outside the variable/zero/succ grammar")

let adapt_term context raw =
  let* _signature = signature context.K.Check.globals in
  let* term = decode ~scope:context.K.Check.size raw in
  let* ty = kernel (K.Eval.eval context.K.Check.globals [] nat_type) in
  let* () = kernel (K.Check.check context Q.Many raw ty) in
  Ok term

type case_view = { source : T.elim; motive : T.motive;
                   zero_branch : T.leg; succ_branch : T.leg }

(* Check the application/type fragment used by the two selected schemas.
   In particular, an SPi application carries a domain that the pinned
   spi_elim_out rule ignores, while the evaluator evaluates it. *)
let rec validate_payloads context raw =
  let eval term = kernel (K.Eval.eval context.K.Check.globals context.K.Check.env term) in
  match raw with
  | T.Var _ | T.Univ _ | T.Global _ -> Ok ()
  | T.Out (Sh.SPi (quantity, _name, domain), T.APt (argument_quantity, argument), head) ->
      let* () = validate_payloads context head in
      let* () = validate_payloads context domain in
      let* () = validate_payloads context argument in
      let* _level = kernel (K.Check.infer_univ context domain) in
      let* head_type = kernel (K.Check.infer context Q.Zero head) in
      let* head_type = kernel (K.Eval.whnf context.K.Check.globals head_type) in
      let* head_shape, _diagram, _universe = K.Value.as_ran head_type
        |> Option.to_result ~none:(missing "application head must have a function type") in
      let* actual_quantity, _name, actual_domain = K.Rules.as_vpi head_shape
        |> Option.to_result ~none:(missing "application head must have an SPi type") in
      let* () = require (quantity = argument_quantity && quantity = actual_quantity)
          "application annotation must match its function quantity" in
      let* annotated_domain = eval domain in
      let* agrees = kernel (K.Conv.conv_type K.Check.ops context annotated_domain actual_domain) in
      require agrees "application annotation must match its function domain"
  | T.Ran (Sh.SPi (quantity, name, domain), codomain) ->
      let* () = validate_payloads context domain in
      let* _level = kernel (K.Check.infer_univ context domain) in
      let* domain_value = eval domain in
      validate_payloads (K.Check.bind name quantity domain_value context) codomain
  | T.Lan (Sh.SMu _, diagram) -> validate_payloads context diagram
  | T.In (Sh.SMu _, _address, arguments) ->
      List.fold_left (fun result term -> let* () = result in
        validate_payloads context term) (Ok ()) arguments
  | T.Sec (Sh.SColl _, legs) ->
      List.fold_left (fun result leg ->
        let* () = result in
        let* () = require (leg.T.l_binders = []) "collection field must bind no variables" in
        validate_payloads context leg.T.l_body) (Ok ()) legs
  | T.Lan _ | T.Ran _ | T.In _ | T.Elim _ | T.Sec _ | T.Out _
  | T.Let _ | T.Ann _ | T.Lit _ | T.Auto ->
      Error (missing "annotation or branch outside the selected application/type schemas")

let adapt_case context source =
  let* _signature = signature context.K.Check.globals in
  let* () = well_scoped context.K.Check.size (T.Elim source) in
  let* () = validate_shapes (T.Elim source) in
  let* () = require (source.T.e_shape = shape) "case has a wrong family or index" in
  let* () = require (source.T.e_scrut_q = Q.One) "case scrutinee quantity must be One" in
  let* motive = source.T.e_motive |> Option.to_result ~none:(missing "explicit motive required") in
  let* () = require (motive.T.m_ind = Some "N" && motive.T.m_idx = [])
      "motive must name N and bind no indices" in
  let* zero_branch, succ_branch =
    match source.T.e_branches with
    | [ (T.ACtor "zero", zero_branch); (T.ACtor "succ", succ_branch) ] ->
        Ok (zero_branch, succ_branch)
    | [] | [ _ ] | [ _; _ ] | _ :: _ :: _ :: _ ->
        Error (missing "case branches must use zero, succ addresses in declaration order")
  in
  let* () = require (zero_branch.T.l_binders = []) "zero branch binds no fields" in
  let* () =
    match succ_branch.T.l_binders with
    | [ (Q.Many, _name) ] -> Ok ()
    | [] | [ (Q.Zero, _) ] | [ (Q.One, _) ] | _ :: _ :: _ ->
        Error (missing "succ branch binds only one Many predecessor and no implicit IH")
  in
  let* _scrutinee = adapt_term context source.T.e_scrut in
  let* nat = kernel (K.Eval.eval context.K.Check.globals [] nat_type) in
  let motive_context = K.Check.bind motive.T.m_self Q.Zero nat context in
  let* () = validate_payloads motive_context motive.T.m_body in
  let* () = validate_payloads context zero_branch.T.l_body in
  let successor_context = K.Check.bind "predecessor" Q.Many nat context in
  let* () = validate_payloads successor_context succ_branch.T.l_body in
  let* level = kernel (K.Check.infer_univ motive_context motive.T.m_body) in
  let* () = require (K.Level.equal level K.Level.one) "motive must be Type0-valued" in
  let* _result_type = kernel (K.Check.infer context Q.Many (T.Elim source)) in
  Ok { source; motive; zero_branch; succ_branch }

let definition globals name =
  K.Global.find_def name globals |> Option.to_result ~none:(missing ("no definition " ^ name))

(* Reconstruct the actual typed contexts while peeling accepted lambdas. *)
let rec open_lambdas context count body =
  match body with
  | T.Sec (Sh.SPi (quantity, name, domain),
      [ { T.l_binders = [ (binder_quantity, binder_name) ]; l_body } ]) ->
      let* () = require (quantity = binder_quantity && String.equal name binder_name)
          "lambda shape and field binder disagree" in
      let* () = validate_payloads context domain in
      let* _level = kernel (K.Check.infer_univ context domain) in
      let* domain_value = kernel (K.Eval.eval context.K.Check.globals context.K.Check.env domain) in
      open_lambdas (K.Check.bind name quantity domain_value context) (count + 1) l_body
  | T.Var _ | T.Univ _ | T.Lan _ | T.Ran _ | T.In _ | T.Elim _ | T.Sec _
  | T.Out _ | T.Let _ | T.Ann _ | T.Global _ | T.Lit _ | T.Auto -> Ok (context, count, body)

let definition_case globals name =
  let* entry = definition globals name in
  let* () = well_scoped 0 entry.K.Global.ty in
  let* () = well_scoped 0 entry.K.Global.def in
  let* () = validate_terms [ entry.K.Global.ty; entry.K.Global.def ] in
  let* ty = kernel (K.Eval.eval globals [] entry.K.Global.ty) in
  let* () = kernel (K.Check.check_term globals entry.K.Global.def ty) in
  let* context, binders, body = open_lambdas (K.Check.make globals K.Budget.unlimited) 0 entry.K.Global.def in
  match body with
  | T.Elim source ->
      let* view = adapt_case context source in
      Ok (context, binders, view)
  | T.Var _ | T.Univ _ | T.Lan _ | T.Ran _ | T.In _ | T.Sec _ | T.Out _
  | T.Let _ | T.Ann _ | T.Global _ | T.Lit _ | T.Auto -> Error (missing "definition body is not a case")

let rec application_spine arguments raw =
  match raw with
  | T.Out (Sh.SPi (quantity, _name, _domain), T.APt (argument_quantity, argument), head) ->
      let* () = require (quantity = argument_quantity) "application quantities disagree" in
      application_spine ((quantity, argument) :: arguments) head
  | T.Var _ | T.Univ _ | T.Lan _ | T.Ran _ | T.In _ | T.Elim _ | T.Sec _
  | T.Out _ | T.Let _ | T.Ann _ | T.Global _ | T.Lit _ | T.Auto -> Ok (raw, arguments)

let validate_induction globals =
  let* entry = definition globals "induction" in
  let* () = require (entry.K.Global.rec_arg = Some 3 && not entry.K.Global.partial)
      "induction must be structurally guarded on its fourth parameter" in
  let* _context, binders, view = definition_case globals "induction" in
  let* () = require (binders = 4 && view.source.T.e_scrut = T.Var 0)
      "induction must have P,z,s,n binders and scrutinize n" in
  let* () = require (view.zero_branch.T.l_body = T.Var 2) "zero branch must return z (DB2)" in
  let* motive_head, motive_args = application_spine [] view.motive.T.m_body in
  let* () = require (motive_head = T.Var 4 && motive_args = [ (Q.Many, T.Var 0) ])
      "dependent motive must apply P (DB4) to self (DB0)" in
  let* step_head, step_args = application_spine [] view.succ_branch.T.l_body in
  let* recursive_call =
    match step_args with
    | [ (Q.Many, T.Var 0); (Q.Many, call) ] -> Ok call
    | [] | [ _ ] | [ _; _ ] | _ :: _ :: _ :: _ ->
        Error (missing "successor step must take predecessor and recursive result")
  in
  let* () = require (step_head = T.Var 2) "successor branch must apply s (DB2)" in
  let* recursive_head, recursive_args = application_spine [] recursive_call in
  let* () = require
      (recursive_head = T.Global "induction"
       && recursive_args = [ (Q.Zero, T.Var 4); (Q.Many, T.Var 3);
                             (Q.Many, T.Var 2); (Q.Many, T.Var 0) ])
      "recursive call must preserve P,z,s and recurse on predecessor DB0" in
  let* certificate = kernel (K.Totality.guard_group globals [ ("induction", entry.K.Global.def) ]) in
  let* certificate = certificate |> Option.to_result ~none:(missing "recursive guard certificate required") in
  let* () = require (certificate.K.Order.o_arg = 3) "guard certificate must select n" in
  let* () =
    match certificate.K.Order.o_rows with
    | [ { K.Order.rw_member = "induction";
          rw_calls = [ { K.Order.cl_callee = "induction";
                         cl_chain = [ { K.Order.st_scrut = 0; st_ctor = Some "succ" } ] } ] } ] -> Ok ()
    | [] | [ _ ] | _ :: _ :: _ -> Error (missing "guard must identify the single succ predecessor call")
  in
  Ok ()

let profile globals =
  let* signature = signature globals in
  let* () = validate_induction globals in
  let* _context, binders, view = definition_case globals "dependentCase" in
  let* () = require (binders = 1) "dependentCase takes one N parameter" in
  let* motive_head, motive_args = application_spine [] view.motive.T.m_body in
  let* () = require (motive_head = T.Global "Fiber" && motive_args = [ (Q.Many, T.Var 0) ])
      "dependentCase motive must apply Fiber to self DB0" in
  Ok (Printf.sprintf
    "{\"family\":\"%s\",\"shape\":\"SMu\",\"parameters\":%d,\"indices\":%d,\"universe\":\"Type0\",\"zero\":{\"address\":\"%s\",\"fields\":%d},\"succ\":{\"address\":\"%s\",\"fields\":[{\"quantity\":\"Many\",\"type\":\"N\",\"db\":0}]},\"motive\":{\"family\":\"N\",\"indices\":%d,\"self_db\":0},\"case\":{\"scrutinee_quantity\":\"One\",\"zero_binders\":%d,\"succ_binders\":%d,\"implicit_ih\":false},\"polynomial\":\"1+X\",\"polynomial_index\":\"Unit\"}"
    signature.family.K.Positivity.f_name (List.length signature.family.K.Positivity.f_params)
    (List.length signature.family.K.Positivity.f_indices) signature.zero_ctor.K.Positivity.c_name
    (List.length signature.zero_ctor.K.Positivity.c_args) signature.succ_ctor.K.Positivity.c_name
    (List.length view.motive.T.m_idx) (List.length view.zero_branch.T.l_binders)
    (List.length view.succ_branch.T.l_binders))
