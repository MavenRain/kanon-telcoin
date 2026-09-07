import KanonTelcoin

namespace KanonTelcoin.Tests
open NatFragmentBridge

-- This concrete external test model does not assert a Kan construction.
abbrev naturalModel : Model := ⟨Nat, 0, Nat.succ⟩

def oneVariable : SourceTerm 1 := .succ (.var ⟨0, Nat.zero_lt_succ 0⟩)

def replacement : Substitution 1 0 := fun _ignored => .succ .zero

example :
    (oneVariable.substitute replacement).interpret naturalModel
      (emptyEnvironment naturalModel) = 2 := rfl

example :
    (oneVariable.substitute replacement).interpret naturalModel
      (emptyEnvironment naturalModel) =
    oneVariable.interpret naturalModel
      (reindexEnvironment naturalModel replacement (emptyEnvironment naturalModel)) :=
  typed_substitution naturalModel replacement (emptyEnvironment naturalModel) oneVariable

example : declarationAccepted canonicalDeclaration = true := rfl

example : declarationAccepted { canonicalDeclaration with indices := 1 } = false := rfl

example : checkTerm canonicalAdmission 0 (.var 1) = .error .illScoped := rfl

example : checkTerm canonicalAdmission 0 (.intro .declaredN [1] .zero []) =
    .error .wrongIndices := rfl

example : checkTerm canonicalAdmission 0 (.intro .opaqueNat [] .zero []) =
    .error .wrongFamily := rfl

example : checkTerm canonicalAdmission 0 (.intro .declaredN [] .succ []) =
    .error .wrongArity := rfl

example : checkTerm canonicalAdmission 0
    (.intro .declaredN [] .succ [.intro .declaredN [] .zero []]) =
    .ok (.succ .zero) := rfl

-- The result type depends on both the scrutinee and a substituted local.
def varyingCase : CaseParameters naturalModel 1 where
  motive := fun environment value => Fin (Nat.succ (value + environment 0))
  zero := fun environment => ⟨0, Nat.zero_lt_succ (0 + environment 0)⟩
  successor := fun environment predecessor =>
    ⟨0, Nat.zero_lt_succ (Nat.succ predecessor + environment 0)⟩

example :
    reindexMotive naturalModel replacement varyingCase.motive
      (emptyEnvironment naturalModel)
      ((oneVariable.substitute replacement).interpret naturalModel
        (emptyEnvironment naturalModel)) = Fin 4 := rfl

example (initial : KanonMeta.Initiality.Initial naturalModel.indexed) :
    (typed_substitution naturalModel replacement (emptyEnvironment naturalModel)
      oneVariable ▸
      interpretCase naturalModel initial (varyingCase.substitute naturalModel replacement)
        (emptyEnvironment naturalModel)
        (CaseCode.substitute replacement { scrutinee := oneVariable })) =
    interpretCase naturalModel initial varyingCase
      (reindexEnvironment naturalModel replacement (emptyEnvironment naturalModel))
      { scrutinee := oneVariable } :=
  case_reindexing naturalModel initial replacement varyingCase
    (emptyEnvironment naturalModel) { scrutinee := oneVariable }

def boundedMotive (value : Nat) : Type := Fin (value + 1)

def boundedZero : boundedMotive 0 := ⟨0, Nat.zero_lt_succ 0⟩

def boundedStep (predecessor : Nat) (previous : boundedMotive predecessor) :
    boundedMotive (Nat.succ predecessor) :=
  ⟨previous.val + 1, Nat.succ_lt_succ previous.isLt⟩

-- Structural evaluation computes dependent evidence, without an Initial premise.
example :
    (evaluateGuarded naturalModel boundedMotive boundedZero boundedStep {}
      (.succ (.succ .zero))).val = 2 := rfl

example (initial : KanonMeta.Initiality.Initial naturalModel.indexed) :
    induction naturalModel initial boundedMotive boundedZero boundedStep 2 =
      evaluateGuarded naturalModel boundedMotive boundedZero boundedStep {}
        (.succ (.succ .zero)) :=
  (guarded_realizes_elim naturalModel initial boundedMotive boundedZero boundedStep {}
    (.succ (.succ .zero))).symm

example : checkRecursiveCall (.var 1) = .error .notPredecessor := rfl

example : checkRecursiveCall (.intro .declaredN [] .zero []) =
    .error .notPredecessor := rfl

end KanonTelcoin.Tests
