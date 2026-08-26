import Formalization.Components.RepeatedStepDefinitions
import Formalization.Components.RankBoxedExtensionDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RepeatedBox

open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.RankBoxedStructure
open BuildingUpFormalization.Components.RankBoxedExtension

variable {K : Type*} [Field K]

/-- The usual scalar coordinates, listing each pair consecutively. -/
def flattenRow {k r : ℕ} (R : RankBoxRow K k r) : Fin ((k + r) * 2) → K :=
  fun j => R (finSumFinEquiv.symm (finProdFinEquiv.symm j).1)
    (finProdFinEquiv.symm j).2

def unflattenRow {k r : ℕ} (v : Fin ((k + r) * 2) → K) : RankBoxRow K k r :=
  fun j t => v (finProdFinEquiv (finSumFinEquiv j, t))

def flattenRows {k r : ℕ} (R : RankBoxIndex k r → RankBoxRow K k r) :
    Matrix (Fin (k + r)) (Fin ((k + r) * 2)) K :=
  fun i => flattenRow (R (finSumFinEquiv.symm i))

/-- The new column below the first pivot, including all terminal rows. -/
def extensionGamma {k r : ℕ} (c : K) (H Q : Fin k → Fin r → K)
    (D : Fin r → Fin r → K) (h q : Fin r → K) (u : Fin k → K) :
    RankBoxIndex k r → K
  | .inl i => c * (∑ t, q t * Q i t) -
      (∑ t, (h t * Q i t + q t * H i t)) - u i
  | .inr s => -(∑ t, q t * D s t)

def extensionTail {k r : ℕ} (c : K) (h q : Fin r → K) (u : Fin k → K) :
    RankBoxRow K k r
  | .inl j => head2 (u j) (c * u j)
  | .inr t => head2 (h t) (c * h t + q t)

/-- Read a larger boxed matrix in the order: new pair, then old pairs. -/
def readSuccessor {k r : ℕ} (R : RankBoxIndex (k + 1) r → RankBoxRow K (k + 1) r) :
    Matrix (Fin (k + r + 1)) (Fin (2 + (k + r) * 2)) K :=
  let row := fun i => prepend2 (R i (.inl 0) 0) (R i (.inl 0) 1)
    (flattenRow (fun j => R i (keepRankBoxIndex (Fin.succEmb k) j)))
  Fin.cons (row (.inl 0))
    (fun i => row (keepRankBoxIndex (Fin.succEmb k) (finSumFinEquiv.symm i)))

/-- Coefficients of the explicit reverse top-row operation; terminal rows
are not used. These are row operations, not coordinate scalings. -/
def reverseCoeff {k r : ℕ} (c : K) (x : Fin ((k + r) * 2) → K) :
    Fin (k + r) → K :=
  fun i => match finSumFinEquiv.symm i with
    | .inl j => -(c * SplitBoxed.blockDefect c (unflattenRow x (.inl j)))
    | .inr _ => 0

def reverseTail {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (x : Fin ((k + r) * 2) → K) : RankBoxRow K k r :=
  c • unflattenRow x - ∑ j, (c * SplitBoxed.blockDefect c (unflattenRow x (.inl j))) •
    rankBoxedRows c P H Q A D (.inl j)

end BuildingUpFormalization.Components.RepeatedBox
