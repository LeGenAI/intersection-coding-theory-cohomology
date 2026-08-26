import Formalization.Components.FoundationsDefinitions
import Formalization.Components.PermutationEquivalenceDefinitions
import Formalization.Components.RankBoxedDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.BinaryRankOneNormalization

open BuildingUpFormalization.Components.Foundations
open BuildingUpFormalization.Components.PermutationEquivalence
open BuildingUpFormalization.Components.RankBoxed

/-- The coordinate equivalence which forgets the displayed two-coordinate
block structure of a rank box.  It is a coordinate permutation, not a general
ambient linear equivalence. -/
def rankBoxCoordEquivFin (k r : ℕ) :
    (RankBoxIndex k r × Fin 2) ≃ Fin (2 * (k + r)) :=
  (Equiv.prodCongr finSumFinEquiv (Equiv.refl (Fin 2))).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm (k + r) 2)))

/-- Flatten a block row without changing any coordinate value. -/
def flattenRankBoxRow {K : Type*} {k r : ℕ}
    (R : RankBoxRow K k r) : Fin (2 * (k + r)) → K :=
  fun j =>
    let p := (rankBoxCoordEquivFin k r).symm j
    R p.1 p.2

/-- Flatten both the row index and the two-coordinate block index. -/
def flattenRankBoxedRows {K : Type*} {k r : ℕ}
    (R : RankBoxIndex k r → RankBoxRow K k r) :
    Fin (k + r) → Fin (2 * (k + r)) → K :=
  fun i => flattenRankBoxRow (R (finSumFinEquiv.symm i))

/-- The literal Chinburg--Zhang rank-one boxed rows as an ordinary
`(k+1) × 2(k+1)` binary generator matrix. -/
def binaryCzRankOneFinRows {k : ℕ}
    (b : Fin k → Fin k → ZMod 2) :
    Fin (k + 1) → Fin (2 * (k + 1)) → ZMod 2 :=
  flattenRankBoxedRows (binaryCzRankOneRows b)

/-- The all-ones word. -/
def allOnes {K : Type*} (n : ℕ) [One K] : Fin n → K :=
  fun _ => 1

/-- Sum of the first two scalar coordinates.  In characteristic two its
kernel is exactly the family whose two head coordinates are equal. -/
def binaryHeadDefectLinear {K : Type*} [Field K] {n : ℕ} :
    (Fin (2 + n) → K) →ₗ[K] K where
  toFun v := v 0 + v 1
  map_add' u v := by simp; ring
  map_smul' a v := by simp; ring

/-- Delete the first two scalar coordinates as a linear map. -/
def binaryTailLinear {K : Type*} [Field K] {n : ℕ} :
    (Fin (2 + n) → K) →ₗ[K] (Fin n → K) where
  toFun := splitTail (K := K)
  map_add' u v := by
    funext j
    rfl
  map_smul' a v := by
    funext j
    rfl

/-- The kernel of the first-coordinate sum restricted to `C`. In
characteristic two this is the equal-coordinate subcode. -/
def binaryShorteningDomain {K : Type*} [Field K] {n : ℕ}
    (C : Submodule K (Fin (2 + n) → K)) : Submodule K C :=
  (binaryHeadDefectLinear (K := K) (n := n)).domRestrict C |>.ker

/-- Delete the first two coordinates on that kernel. The name is retained
for compatibility; this is not ordinary zero-coordinate shortening. -/
def binaryShorteningMap {K : Type*} [Field K] {n : ℕ}
    (C : Submodule K (Fin (2 + n) → K)) :
    binaryShorteningDomain C →ₗ[K] (Fin n → K) :=
  (binaryTailLinear (K := K) (n := n)).comp
    (C.subtype.comp (binaryShorteningDomain C).subtype)

/-- The two-coordinate reduction used in the Chinburg--Zhang induction.
Over F₂ it retains equal coordinates (00 or 11), then deletes them. -/
def binaryShortenedCode {K : Type*} [Field K] {n : ℕ}
    (C : Submodule K (Fin (2 + n) → K)) : Submodule K (Fin n → K) :=
  (binaryShorteningMap C).range

/-- A scalar-coordinate permutation sending two distinct selected positions
to the first two coordinates, in the order needed for an oriented `01` pivot. -/
def pairToHeadPerm {n : ℕ} (i j : Fin (2 + n)) :
    Equiv.Perm (Fin (2 + n)) :=
  (Equiv.swap 1 ((Equiv.swap 0 i).symm j)).trans (Equiv.swap 0 i)

/-- Exact reverse-normalization goal.

It says that an arbitrary binary code of positive even length is carried by
one permutation of its scalar coordinate positions to the row space of a
literal rank-one Chinburg--Zhang box.  The diagonal and opposite-block laws
are included in the proposition rather than hidden in the constructor. -/
def HasBinaryCzRankOneNormalForm {k : ℕ}
    (C : Submodule (ZMod 2) (Fin (2 * (k + 1)) → ZMod 2)) : Prop :=
  ∃ (σ : Equiv.Perm (Fin (2 * (k + 1))))
      (b : Fin k → Fin k → ZMod 2),
    (∀ i, b i i = 0) ∧
    (∀ i j, i ≠ j → b i j + b j i = 1) ∧
    permutedCode σ C = rowSpace (binaryCzRankOneFinRows b)

end BuildingUpFormalization.Components.BinaryRankOneNormalization
