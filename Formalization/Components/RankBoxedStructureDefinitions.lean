import Formalization.Components.RankBoxedDefinitions
import Formalization.Components.QaryRankBoxedNormalizationDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RankBoxedStructure

open BuildingUpFormalization.Components.SplitBoxed
open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.QaryRankBoxedNormalization

variable {K : Type*} [Field K]

/-- Keep the selected pivot indices and every master index. -/
def keepRankBoxIndex {l k r : ℕ} (s : Fin l ↪ Fin k) :
    RankBoxIndex l r → RankBoxIndex k r := Sum.map s id

/-- Delete unselected pivot rows AND their two-coordinate block columns.
This is not puncturing the entire original code. -/
def restrictRankBoxRows {l k r : ℕ} (s : Fin l ↪ Fin k)
    (R : RankBoxIndex k r → RankBoxRow K k r) :
    RankBoxIndex l r → RankBoxRow K l r :=
  fun i j => R (keepRankBoxIndex s i) (keepRankBoxIndex s j)

/-- The exact index identification for the rank-one specialization. -/
def rankOneOptionEquiv (k : ℕ) : RankBoxIndex k 1 ≃ Option (Fin k) where
  toFun x := match x with | .inl i => some i | .inr _ => none
  invFun x := match x with | some i => .inl i | none => .inr 0
  left_inv x := by
    cases x with
    | inl i => rfl
    | inr t =>
      have ht : t = 0 := Subsingleton.elim _ _
      subst t
      rfl
  right_inv x := by cases x <;> rfl

/-- The diagonal-zero condition is explicit, not inferred from rank one. -/
def specializationP {k : ℕ} (b : Fin k → Fin k → K) : Fin k → Fin k → K :=
  fun i j => if i = j then 0 else b i j

def specializationH {k : ℕ} (ell : Fin k → SplitBlock K) : Fin k → Fin 1 → K :=
  fun i _ => ell i 0

def specializationQ {k : ℕ} (c : K) (ell : Fin k → SplitBlock K) :
    Fin k → Fin 1 → K := fun i _ => ell i 1 - c * ell i 0

def specializationA {k : ℕ} (a : Fin k → K) : Fin 1 → Fin k → K :=
  fun _ i => a i

def unitCore : Fin 1 → Fin 1 → K := fun _ _ => 1

end BuildingUpFormalization.Components.RankBoxedStructure
