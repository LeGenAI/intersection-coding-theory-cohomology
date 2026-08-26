import Formalization.Components.PermutationEquivalenceDefinitions
import Formalization.Components.Foundations

set_option autoImplicit false

open BuildingUpFormalization.Components.Foundations

namespace BuildingUpFormalization.Components.PermutationEquivalence

variable {K : Type*} [Field K]

@[simp] theorem coordinatePermuteLinearEquiv_apply
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → K) :
    coordinatePermuteLinearEquiv (K := K) σ v = permuteVec σ v := by
  sorry

theorem dot_coordinatePermuteLinearEquiv
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (u v : Fin n → K) :
    dot (permuteVec σ u) (permuteVec σ v) = dot u v := by
  sorry

theorem rowSpace_permuteFamily_eq_permutedCode
    {m n : ℕ} (σ : Equiv.Perm (Fin n)) (R : Fin m → Fin n → K) :
    rowSpace (permuteFamily σ R) =
      permutedCode (K := K) σ (rowSpace R) := by
  sorry

theorem paperSelfDualCode_permutedCode
    {n : ℕ} (σ : Equiv.Perm (Fin n)) {C : Submodule K (Fin n → K)}
    (hC : paperSelfDualCode (K := K) C) :
    paperSelfDualCode (K := K) (permutedCode (K := K) σ C) := by
  sorry

theorem codeEquiv_preserves_paperSelfDualCode
    {m₁ m₂ n : ℕ} {R : Fin m₁ → Fin n → K} {S : Fin m₂ → Fin n → K}
    (hRS : CodeEquiv R S)
    (hR : paperSelfDualCode (K := K) (rowSpace R)) :
    paperSelfDualCode (K := K) (rowSpace S) := by
  sorry

end BuildingUpFormalization.Components.PermutationEquivalence
