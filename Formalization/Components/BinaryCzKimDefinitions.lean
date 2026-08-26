import Formalization.Components.FoundationsDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.BinaryCzKim

open BuildingUpFormalization.Components.Foundations

variable {K : Type*} [Field K]

/-- The diagonal vector `(1,1)` in the standard two-coordinate Euclidean plane. -/
def binaryDiagonalHead : Plane K := planeE0 + planeE1

/-- Delete the top row and its first two coordinates from a binary boxed family.
The name is deliberately coordinate-theoretic: the head plane is Euclidean and
non-alternating, not an alternating hyperbolic plane. -/
def deleteBinaryHeadPair {m n : ℕ}
    (R : Fin (m + 1) → Fin (2 + n) → K) : Fin m → Fin n → K :=
  deleteHyperbolicPair R

/-- The linear operation sending a binary parent row to its Kim successor row. -/
def buildSuccBinLinear {n : ℕ} (x : Fin n → K) :
    (Fin n → K) →ₗ[K] (Fin (2 + n) → K) where
  toFun g := riBin (dot x g) g
  map_add' g h := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro k
      fin_cases k <;> simp [riBin, prepend2, head2, dot_add_right]
    · intro k
      simp [riBin, prepend2]
  map_smul' a g := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro k
      fin_cases k <;> simp [riBin, prepend2, head2, dot_smul_right]
    · intro k
      simp [riBin, prepend2]

end BuildingUpFormalization.Components.BinaryCzKim
