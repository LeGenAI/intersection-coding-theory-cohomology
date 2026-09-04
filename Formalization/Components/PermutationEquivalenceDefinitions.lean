import Formalization.Components.FoundationsDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.PermutationEquivalence

variable {K : Type*} [Field K]

/-- The linear equivalence obtained by permuting coordinate positions.
For row vectors this is the action denoted by right multiplication `u P_σ`
in Definition 2.3 of the paper. -/
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

/-- The image of a code under the row-vector right action of a coordinate
permutation matrix. -/
def permutedCode {n : ℕ} (σ : Equiv.Perm (Fin n))
    (C : Submodule K (Fin n → K)) : Submodule K (Fin n → K) :=
  C.map (coordinatePermuteLinearEquiv (K := K) σ).toLinearMap

end BuildingUpFormalization.Components.PermutationEquivalence
