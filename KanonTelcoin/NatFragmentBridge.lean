import KanonMeta.Initiality

/-!
Conditional semantics of the closed unary `N` declaration and a parametric
dependent case/structural-recursion schema. Motive and branch operations are
typed parameters, not an encoding of the compiler's entire term language.
Locals have type N. Dependent results live in Type 0. Initiality is a premise;
semantic computation is propositional and supplies no source conversion rule.
-/

namespace KanonTelcoin.NatFragmentBridge
open KanonMeta.Initiality

inductive Quantity where
  | zero | one | many
  deriving DecidableEq, Repr

inductive Family where
  | declaredN | opaqueNat
  deriving DecidableEq, Repr

inductive Address where
  | zero | succ
  deriving DecidableEq, Repr

def Address.name : Address → String
  | .zero => "zero"
  | .succ => "succ"

structure Field where
  quantity : Quantity
  family : Family
  deriving DecidableEq, Repr

structure Constructor where
  address : Address
  fields : List Field
  resultIndices : List Nat
  deriving DecidableEq, Repr

structure Declaration where
  family : Family
  name : String
  level : Nat
  parameters : Nat
  indices : Nat
  constructors : List Constructor
  deriving DecidableEq, Repr

def canonicalDeclaration : Declaration :=
  ⟨.declaredN, "N", 0, 0, 0, [⟨.zero, [], []⟩, ⟨.succ, [⟨.many, .declaredN⟩], []⟩]⟩

def declarationAccepted (declaration : Declaration) : Bool :=
  decide (declaration = canonicalDeclaration)

/-- Whole-signature admission, not a family-name comparison. -/
structure AcceptedDeclaration where
  declaration : Declaration
  agrees : declaration = canonicalDeclaration

def canonicalAdmission : AcceptedDeclaration := ⟨canonicalDeclaration, rfl⟩

theorem canonical_declaration_accepted :
    declarationAccepted canonicalDeclaration = true := rfl

inductive Shape where
  | zero | succ
  deriving DecidableEq, Repr

def polynomial : Polynomial Unit where
  Shape := fun (_index : Unit) => Shape
  Position := fun shape => match shape with
    | .zero => Empty
    | .succ => Unit
  child := fun _ (_position) => ()

def addressShape : Address → Shape
  | .zero => .zero
  | .succ => .succ

def polynomialLayer (X : Type) := (shape : Shape) × (polynomial.Position (i := ()) shape → X)

def toSum {X : Type} : polynomialLayer X → Sum Unit X
  | ⟨.zero, _⟩ => .inl ()
  | ⟨.succ, children⟩ => .inr (children ())

def fromSum {X : Type} : Sum Unit X → polynomialLayer X
  | .inl () => ⟨.zero, Empty.elim⟩
  | .inr child => ⟨.succ, fun (_position : Unit) => child⟩

theorem toSum_fromSum {X : Type} : (layer : Sum Unit X) → toSum (fromSum layer) = layer
  | .inl () => rfl
  | .inr (_child) => rfl

theorem fromSum_toSum {X : Type} :
    (layer : polynomialLayer X) → fromSum (toSum layer) = layer
  | ⟨.zero, _children⟩ => congrArg (fun xs => (⟨.zero, xs⟩ : polynomialLayer X))
      (funext (fun position => Empty.elim position))
  | ⟨.succ, _children⟩ => congrArg (fun xs => (⟨.succ, xs⟩ : polynomialLayer X))
      (funext (fun () => rfl))

structure Model where
  Carrier : Type
  zero : Carrier
  succ : Carrier → Carrier

def Model.indexed (model : Model) : Algebra polynomial where
  Carrier := fun (_index : Unit) => model.Carrier
  roll := fun shape children => match shape with
    | .zero => model.zero
    | .succ => model.succ (children ())

def displayed (model : Model) (motive : model.Carrier → Type)
    (zero : motive model.zero)
    (step : (predecessor : model.Carrier) → motive predecessor →
      motive (model.succ predecessor)) : Displayed model.indexed where
  Fibre := motive
  step := fun shape children hypotheses => match shape with
    | .zero => zero
    | .succ => step (children ()) (hypotheses ())

def induction (model : Model) (initial : Initial model.indexed)
    (motive : model.Carrier → Type) (zero : motive model.zero)
    (step : (predecessor : model.Carrier) → motive predecessor →
      motive (model.succ predecessor)) (value : model.Carrier) : motive value :=
  elim initial (displayed model motive zero step) (i := ()) value

theorem induction_beta_zero (model : Model) (initial : Initial model.indexed)
    (motive : model.Carrier → Type) (zero : motive model.zero)
    (step : (predecessor : model.Carrier) → motive predecessor →
      motive (model.succ predecessor)) :
    induction model initial motive zero step model.zero = zero :=
  elim_beta initial (displayed model motive zero step) (i := ()) .zero Empty.elim

theorem induction_beta_succ (model : Model) (initial : Initial model.indexed)
    (motive : model.Carrier → Type) (zero : motive model.zero)
    (step : (predecessor : model.Carrier) → motive predecessor →
      motive (model.succ predecessor)) (predecessor : model.Carrier) :
    induction model initial motive zero step (model.succ predecessor) =
      step predecessor (induction model initial motive zero step predecessor) :=
  elim_beta initial (displayed model motive zero step) (i := ()) .succ (fun (_ : Unit) => predecessor)

/-- Intrinsic N-typing and scope; motive and branches are separate parameters. -/
inductive SourceTerm (scope : Nat) where
  | var (index : Fin scope)
  | zero
  | succ (predecessor : SourceTerm scope)
  deriving Repr

inductive RawTerm where
  | var (index : Nat)
  | intro (family : Family) (indices : List Nat) (address : Address) (fields : List RawTerm)
  deriving Repr

inductive ScopeError where
  | illScoped | wrongFamily | wrongIndices | wrongArity
  deriving DecidableEq, Repr

def checkTerm (_admission : AcceptedDeclaration) (scope : Nat) :
    RawTerm → Except ScopeError (SourceTerm scope)
  | .var index => if bound : index < scope then .ok (.var ⟨index, bound⟩)
      else .error .illScoped
  | .intro .opaqueNat _ _ (_fields) => .error .wrongFamily
  | .intro .declaredN (_ :: _) _ (_fields) => .error .wrongIndices
  | .intro .declaredN [] .zero [] => .ok .zero
  | .intro .declaredN [] .zero (_ :: _) => .error .wrongArity
  | .intro .declaredN [] .succ [] => .error .wrongArity
  | .intro .declaredN [] .succ [predecessor] =>
      (checkTerm _admission scope predecessor).map .succ
  | .intro .declaredN [] .succ (_ :: _ :: _) => .error .wrongArity

def SourceTerm.raw {scope : Nat} : SourceTerm scope → RawTerm
  | .var index => .var index.val
  | .zero => .intro .declaredN [] .zero []
  | .succ predecessor => .intro .declaredN [] .succ [predecessor.raw]

/-- Every intrinsic source term passes the raw scope/signature adapter. -/
theorem checkTerm_raw (admission : AcceptedDeclaration) {scope : Nat} :
    (term : SourceTerm scope) → checkTerm admission scope term.raw = .ok term
  | .var index => dif_pos index.isLt
  | .zero => rfl
  | .succ predecessor => congrArg (Except.map SourceTerm.succ)
      (checkTerm_raw admission predecessor)

theorem wrong_index_rejected :
    checkTerm canonicalAdmission 0 (.intro .declaredN [0] .zero []) = .error .wrongIndices := rfl

theorem ill_scoped_rejected :
    checkTerm canonicalAdmission 0 (.var 0) = .error .illScoped := rfl

theorem opaque_nat_rejected :
    checkTerm canonicalAdmission 0 (.intro .opaqueNat [] .zero []) = .error .wrongFamily := rfl

abbrev Environment (model : Model) (scope : Nat) := Fin scope → model.Carrier

def emptyEnvironment (model : Model) : Environment model 0 := Fin.elim0

def SourceTerm.interpret (model : Model) {scope : Nat}
    (environment : Environment model scope) : SourceTerm scope → model.Carrier
  | .var index => environment index
  | .zero => model.zero
  | .succ predecessor => model.succ (predecessor.interpret model environment)

abbrev Substitution (source target : Nat) := Fin source → SourceTerm target

def SourceTerm.substitute {source target : Nat} (substitution : Substitution source target) :
    SourceTerm source → SourceTerm target
  | .var index => substitution index
  | .zero => .zero
  | .succ predecessor => .succ (predecessor.substitute substitution)

def reindexEnvironment (model : Model) {source target : Nat}
    (substitution : Substitution source target) (environment : Environment model target) :
    Environment model source := fun index => (substitution index).interpret model environment

theorem typed_substitution (model : Model) {source target : Nat}
    (substitution : Substitution source target) (environment : Environment model target) :
    (term : SourceTerm source) →
      (term.substitute substitution).interpret model environment =
        term.interpret model (reindexEnvironment model substitution environment)
  | .var (_index) => rfl
  | .zero => rfl
  | .succ predecessor => congrArg model.succ
      (typed_substitution model substitution environment predecessor)

/-- Precisely the motive self variable at de Bruijn index zero. -/
inductive MotiveCode where
  | applyParameterToSelf
  deriving DecidableEq, Repr

def MotiveCode.selfIndex (_code : MotiveCode) : Fin 1 := 0

/-- Case branches receive fields only, without an induction hypothesis. -/
inductive ZeroBranch where
  | parameter
  deriving DecidableEq, Repr

inductive SuccessorBranch where
  | applyParameterToPredecessor
  deriving DecidableEq, Repr

def SuccessorBranch.fieldBinders (_branch : SuccessorBranch) : List Field :=
  [⟨.many, .declaredN⟩]

def SuccessorBranch.predecessorIndex (_branch : SuccessorBranch) : Fin 1 := 0

structure CaseCode (scope : Nat) where
  scrutinee : SourceTerm scope
  motive : MotiveCode := .applyParameterToSelf
  zeroBranch : ZeroBranch := .parameter
  successorBranch : SuccessorBranch := .applyParameterToPredecessor

def CaseCode.scrutineeQuantity {scope : Nat} (_code : CaseCode scope) : Quantity := .one

abbrev Motive (model : Model) (scope : Nat) :=
  Environment model scope → model.Carrier → Type

/-- Typed branch parameters. The successor receives only the predecessor. -/
structure CaseParameters (model : Model) (scope : Nat) where
  motive : Motive model scope
  zero : (environment : Environment model scope) → motive environment model.zero
  successor : (environment : Environment model scope) → (predecessor : model.Carrier) →
    motive environment (model.succ predecessor)

def interpretMotive (model : Model) {scope : Nat} (code : MotiveCode)
    (motive : Motive model scope) (environment : Environment model scope)
    (self : model.Carrier) : Type :=
  motive environment ((fun _ : Fin 1 => self) code.selfIndex)

def interpretZeroBranch (model : Model) {scope : Nat} (_branch : ZeroBranch)
    (parameters : CaseParameters model scope) (environment : Environment model scope) :
    parameters.motive environment model.zero := parameters.zero environment

def interpretSuccessorBranch (model : Model) {scope : Nat} (branch : SuccessorBranch)
    (parameters : CaseParameters model scope) (environment : Environment model scope)
    (predecessor : model.Carrier) : parameters.motive environment (model.succ predecessor) :=
  parameters.successor environment ((fun _ : Fin 1 => predecessor) branch.predecessorIndex)

def interpretCase (model : Model) (initial : Initial model.indexed) {scope : Nat}
    (parameters : CaseParameters model scope) (environment : Environment model scope)
    (code : CaseCode scope) :
    interpretMotive model code.motive parameters.motive environment
      (code.scrutinee.interpret model environment) :=
  induction model initial (parameters.motive environment)
    (interpretZeroBranch model code.zeroBranch parameters environment)
    (fun predecessor (_hypothesis) =>
      interpretSuccessorBranch model code.successorBranch parameters environment predecessor)
    (code.scrutinee.interpret model environment)

inductive CaseReduct (scope : Nat) where
  | zeroParameter
  | successorParameter (predecessor : SourceTerm scope)

def CaseReduct.scrutinee {scope : Nat} : CaseReduct scope → SourceTerm scope
  | .zeroParameter => .zero
  | .successorParameter predecessor => .succ predecessor

inductive CaseBeta {scope : Nat} : CaseCode scope → CaseReduct scope → Prop where
  | zero (motive : MotiveCode) (zero : ZeroBranch) (succ : SuccessorBranch) :
      CaseBeta ⟨.zero, motive, zero, succ⟩ .zeroParameter
  | succ (predecessor : SourceTerm scope) (motive : MotiveCode)
      (zero : ZeroBranch) (succ : SuccessorBranch) :
      CaseBeta ⟨.succ predecessor, motive, zero, succ⟩ (.successorParameter predecessor)

def interpretCaseReduct (model : Model) {scope : Nat}
    (parameters : CaseParameters model scope) (environment : Environment model scope) :
    (reduct : CaseReduct scope) →
      parameters.motive environment (reduct.scrutinee.interpret model environment)
  | .zeroParameter => parameters.zero environment
  | .successorParameter predecessor =>
      parameters.successor environment (predecessor.interpret model environment)

theorem case_beta_zero (model : Model) (initial : Initial model.indexed) {scope : Nat}
    (parameters : CaseParameters model scope) (environment : Environment model scope)
    (motive : MotiveCode) (zero : ZeroBranch) (succ : SuccessorBranch) :
    interpretCase model initial parameters environment ⟨.zero, motive, zero, succ⟩ =
      interpretCaseReduct model parameters environment .zeroParameter :=
  induction_beta_zero model initial (parameters.motive environment)
    (parameters.zero environment) (fun predecessor (_hypothesis) => parameters.successor environment predecessor)

theorem case_beta_succ (model : Model) (initial : Initial model.indexed) {scope : Nat}
    (parameters : CaseParameters model scope) (environment : Environment model scope)
    (predecessor : SourceTerm scope) (motive : MotiveCode)
    (zero : ZeroBranch) (succ : SuccessorBranch) :
    interpretCase model initial parameters environment ⟨.succ predecessor, motive, zero, succ⟩ =
      interpretCaseReduct model parameters environment (.successorParameter predecessor) :=
  induction_beta_succ model initial (parameters.motive environment)
    (parameters.zero environment) (fun predecessor (_hypothesis) => parameters.successor environment predecessor)
    (predecessor.interpret model environment)

theorem case_beta_preservation (model : Model) (initial : Initial model.indexed)
    {scope : Nat} (parameters : CaseParameters model scope)
    (environment : Environment model scope) {code : CaseCode scope}
    {reduct : CaseReduct scope} (step : CaseBeta code reduct) :
    HEq (interpretCase model initial parameters environment code)
      (interpretCaseReduct model parameters environment reduct) :=
  match step with
  | .zero motive zero succ => heq_of_eq
      (case_beta_zero model initial parameters environment motive zero succ)
  | .succ predecessor motive zero succ => heq_of_eq
      (case_beta_succ model initial parameters environment predecessor motive zero succ)

def CaseCode.substitute {source target : Nat} (substitution : Substitution source target)
    (code : CaseCode source) : CaseCode target :=
  { code with scrutinee := code.scrutinee.substitute substitution }

def reindexMotive (model : Model) {source target : Nat}
    (substitution : Substitution source target) (motive : Motive model source) :
    Motive model target := fun environment =>
  motive (reindexEnvironment model substitution environment)

def CaseParameters.substitute (model : Model) {source target : Nat}
    (substitution : Substitution source target) (parameters : CaseParameters model source) :
    CaseParameters model target where
  motive := reindexMotive model substitution parameters.motive
  zero := fun environment => parameters.zero (reindexEnvironment model substitution environment)
  successor := fun environment =>
    parameters.successor (reindexEnvironment model substitution environment)

theorem motive_reindexing (model : Model) {source target : Nat}
    (substitution : Substitution source target) (motive : Motive model source)
    (environment : Environment model target) (term : SourceTerm source) :
    reindexMotive model substitution motive environment
        ((term.substitute substitution).interpret model environment) =
      motive (reindexEnvironment model substitution environment)
        (term.interpret model (reindexEnvironment model substitution environment)) :=
  congrArg (motive (reindexEnvironment model substitution environment))
    (typed_substitution model substitution environment term)

/-- Reindexing needs dependent transport rather than a nondependent fold law. -/
theorem transport_application {X : Type} {P : X → Type}
    (function : (x : X) → P x) {x y : X} (equality : x = y) :
    (equality ▸ function x) = function y :=
  Eq.rec (motive := fun value proof => (proof ▸ function x) = function value) rfl equality

theorem case_reindexing (model : Model) (initial : Initial model.indexed)
    {source target : Nat} (substitution : Substitution source target)
    (parameters : CaseParameters model source) (environment : Environment model target)
    (code : CaseCode source) :
    (typed_substitution model substitution environment code.scrutinee ▸
      interpretCase model initial (parameters.substitute model substitution) environment
        (code.substitute substitution)) =
      interpretCase model initial parameters
        (reindexEnvironment model substitution environment) code :=
  transport_application
    (induction model initial
      (parameters.motive (reindexEnvironment model substitution environment))
      (parameters.zero (reindexEnvironment model substitution environment))
      (fun predecessor (_hypothesis) => parameters.successor
        (reindexEnvironment model substitution environment) predecessor))
    (typed_substitution model substitution environment code.scrutinee)

/-- The sole admitted recursive call is explicitly on the successor field. -/
inductive RecursiveCall where
  | predecessor
  deriving DecidableEq, Repr

def RecursiveCall.argument (_call : RecursiveCall) : SourceTerm 1 := .var 0

inductive GuardError where
  | notPredecessor
  deriving DecidableEq, Repr

def checkRecursiveCall : RawTerm → Except GuardError RecursiveCall
  | .var 0 => .ok .predecessor
  | .var (Nat.succ _) => .error .notPredecessor
  | .intro _ _ _ (_fields) => .error .notPredecessor

theorem nondecreasing_call_rejected :
    checkRecursiveCall (.var 1) = .error .notPredecessor := rfl

structure GuardedSuccessorBranch where
  field : SuccessorBranch := .applyParameterToPredecessor
  call : RecursiveCall := .predecessor
  deriving DecidableEq, Repr

structure GuardedCode (scope : Nat) where
  scrutinee : SourceTerm scope
  motive : MotiveCode := .applyParameterToSelf
  zeroBranch : ZeroBranch := .parameter
  successorBranch : GuardedSuccessorBranch := {}

structure InductionParameters (model : Model) (scope : Nat) where
  motive : Motive model scope
  zero : (environment : Environment model scope) → motive environment model.zero
  step : (environment : Environment model scope) → (predecessor : model.Carrier) →
    motive environment predecessor → motive environment (model.succ predecessor)

def GuardedCode.substitute {source target : Nat} (substitution : Substitution source target)
    (code : GuardedCode source) : GuardedCode target :=
  { code with scrutinee := code.scrutinee.substitute substitution }

def InductionParameters.substitute (model : Model) {source target : Nat}
    (substitution : Substitution source target) (parameters : InductionParameters model source) :
    InductionParameters model target where
  motive := reindexMotive model substitution parameters.motive
  zero := fun environment => parameters.zero (reindexEnvironment model substitution environment)
  step := fun environment => parameters.step (reindexEnvironment model substitution environment)

/-- Structural source evaluation. The predecessor call is the single permitted
recursive argument; neither Initial nor a semantic fold occurs in this definition. -/
def evaluateGuarded (model : Model) (motive : model.Carrier → Type)
    (zero : motive model.zero)
    (step : (predecessor : model.Carrier) → motive predecessor →
      motive (model.succ predecessor)) (branch : GuardedSuccessorBranch) :
    (term : SourceTerm 0) → motive (term.interpret model (emptyEnvironment model))
  | .var index => Fin.elim0 index
  | .zero => zero
  | .succ predecessor =>
      step ((fun (_index : Fin 1) => predecessor.interpret model (emptyEnvironment model))
          branch.field.predecessorIndex)
        (evaluateGuarded model motive zero step branch
          (branch.call.argument.substitute (fun (_index : Fin 1) => predecessor)))

theorem guarded_realizes_elim (model : Model) (initial : Initial model.indexed)
    (motive : model.Carrier → Type) (zero : motive model.zero)
    (step : (predecessor : model.Carrier) → motive predecessor →
      motive (model.succ predecessor)) (branch : GuardedSuccessorBranch) :
    (term : SourceTerm 0) →
      evaluateGuarded model motive zero step branch term =
        induction model initial motive zero step
          (term.interpret model (emptyEnvironment model))
  | .var index => Fin.elim0 index
  | .zero => (induction_beta_zero model initial motive zero step).symm
  | .succ predecessor =>
      (congrArg (step (predecessor.interpret model (emptyEnvironment model)))
        (guarded_realizes_elim model initial motive zero step branch predecessor)).trans
      (induction_beta_succ model initial motive zero step
        (predecessor.interpret model (emptyEnvironment model))).symm

def interpretGuarded (model : Model) (initial : Initial model.indexed) {scope : Nat}
    (parameters : InductionParameters model scope) (environment : Environment model scope)
    (code : GuardedCode scope) :
    parameters.motive environment (code.scrutinee.interpret model environment) :=
  induction model initial (parameters.motive environment) (parameters.zero environment)
    (parameters.step environment) (code.scrutinee.interpret model environment)

theorem induction_reindexing (model : Model) (initial : Initial model.indexed)
    {source target : Nat} (substitution : Substitution source target)
    (parameters : InductionParameters model source) (environment : Environment model target)
    (code : GuardedCode source) :
    (typed_substitution model substitution environment code.scrutinee ▸
      interpretGuarded model initial (parameters.substitute model substitution) environment
        (code.substitute substitution)) =
      interpretGuarded model initial parameters
        (reindexEnvironment model substitution environment) code :=
  transport_application
    (induction model initial
      (parameters.motive (reindexEnvironment model substitution environment))
      (parameters.zero (reindexEnvironment model substitution environment))
      (parameters.step (reindexEnvironment model substitution environment)))
    (typed_substitution model substitution environment code.scrutinee)

/-- An outer-constructor observation for every model satisfying Initial. -/
def observationModel : Model := ⟨Bool, false, fun (_predecessor : Bool) => true⟩

def observe (model : Model) (initial : Initial model.indexed) (value : model.Carrier) : Bool :=
  (initial.fold observationModel.indexed).map (i := ()) value

theorem observe_zero (model : Model) (initial : Initial model.indexed) :
    observe model initial model.zero = false :=
  (initial.fold observationModel.indexed).comm (i := ()) .zero Empty.elim

theorem observe_succ (model : Model) (initial : Initial model.indexed)
    (predecessor : model.Carrier) : observe model initial (model.succ predecessor) = true :=
  (initial.fold observationModel.indexed).comm (i := ()) .succ (fun (_position : Unit) => predecessor)

theorem zero_ne_succ_zero (model : Model) (initial : Initial model.indexed) :
    model.zero ≠ model.succ model.zero := fun equality =>
  Bool.noConfusion ((observe_zero model initial).symm.trans
    ((congrArg (observe model initial) equality).trans (observe_succ model initial model.zero)))

private def profileString (value : String) : String := "\"" ++ value ++ "\""

private def profileObject (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map (fun (name, value) =>
    profileString name ++ ":" ++ value)) ++ "}"

private def quantityName : Quantity → String
  | .zero => "Zero"
  | .one => "One"
  | .many => "Many"

private def familyName : Family → String
  | .declaredN => "N"
  | .opaqueNat => "Nat"

private def fieldProfile (field : Field) : String :=
  profileObject [("quantity", profileString (quantityName field.quantity)),
    ("type", profileString (familyName field.family)),
    ("db", toString SuccessorBranch.applyParameterToPredecessor.predecessorIndex.val)]

private def zeroProfile : String :=
  match canonicalDeclaration.constructors[0]? with
  | none => "null"
  | some constructor => profileObject [("address", profileString constructor.address.name),
      ("fields", toString constructor.fields.length)]

private def successorProfile : String :=
  match canonicalDeclaration.constructors[1]? with
  | none => "null"
  | some constructor => profileObject [("address", profileString constructor.address.name),
      ("fields", "[" ++ String.intercalate "," (constructor.fields.map fieldProfile) ++ "]")]

/-- Deterministic profile of this fixed ASCII-named fragment, independently
compared with the OCaml adapter's validated compiler AST. This is a fixture
agreement check, not a theorem proving the external adapter correct. -/
def profileJson : String :=
  profileObject [
    ("family", profileString canonicalDeclaration.name),
    ("shape", profileString "SMu"),
    ("parameters", toString canonicalDeclaration.parameters),
    ("indices", toString canonicalDeclaration.indices),
    ("universe", profileString ("Type" ++ toString canonicalDeclaration.level)),
    ("zero", zeroProfile),
    ("succ", successorProfile),
    ("motive", profileObject [("family", profileString canonicalDeclaration.name),
      ("indices", toString canonicalDeclaration.indices),
      ("self_db", toString MotiveCode.applyParameterToSelf.selfIndex.val)]),
    ("case", profileObject [
      ("scrutinee_quantity", profileString (quantityName
        (CaseCode.scrutineeQuantity ({ scrutinee := .zero } : CaseCode 0)))),
      ("zero_binders", "0"),
      ("succ_binders", toString SuccessorBranch.applyParameterToPredecessor.fieldBinders.length),
      ("implicit_ih", "false")]),
    ("polynomial", profileString "1+X"),
    ("polynomial_index", profileString "Unit")]

end KanonTelcoin.NatFragmentBridge
