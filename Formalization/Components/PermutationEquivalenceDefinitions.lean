import Formalization.Components.FoundationsDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.PermutationEquivalence

variable {K : Type*} [Field K]

/-- The linear equivalence obtained by permuting coordinate positions. -/
def coordinatePermuteLinearEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) where
  toFun := permuteVec σ
  invFun := permuteVec σ.symm
  left_inv v := by
    funext j
    simp [permuteVec]
  right_inv v := by
    funext j
    simp [permuteVec]
  map_add' u v := by
    funext j
    rfl
  map_smul' a v := by
    funext j
    rfl

/-- The image of a code under a coordinate permutation. -/
def permutedCode {n : ℕ} (σ : Equiv.Perm (Fin n))
    (C : Submodule K (Fin n → K)) : Submodule K (Fin n → K) :=
  C.map (coordinatePermuteLinearEquiv (K := K) σ).toLinearMap

end BuildingUpFormalization.Components.PermutationEquivalence
