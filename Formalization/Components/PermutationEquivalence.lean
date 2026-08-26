import Formalization.Components.PermutationEquivalenceDefinitions
import Formalization.Components.Foundations

set_option autoImplicit false

open BuildingUpFormalization.Components.Foundations

namespace BuildingUpFormalization.Components.PermutationEquivalence

variable {K : Type*} [Field K]

@[simp] theorem coordinatePermuteLinearEquiv_apply
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → K) :
    coordinatePermuteLinearEquiv (K := K) σ v = permuteVec σ v := by
  rfl

theorem dot_coordinatePermuteLinearEquiv
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (u v : Fin n → K) :
    dot (permuteVec σ u) (permuteVec σ v) = dot u v := by
  unfold dot
  simpa [coordinatePermuteLinearEquiv, permuteVec] using
    (Equiv.sum_comp σ (fun j : Fin n => u j * v j))

theorem rowSpace_permuteFamily_eq_permutedCode
    {m n : ℕ} (σ : Equiv.Perm (Fin n)) (R : Fin m → Fin n → K) :
    rowSpace (permuteFamily σ R) =
      permutedCode (K := K) σ (rowSpace R) := by
  unfold rowSpace permutedCode
  rw [Submodule.map_span]
  congr 1
  ext v
  simp [permuteFamily, coordinatePermuteLinearEquiv]

theorem paperSelfDualCode_permutedCode
    {n : ℕ} (σ : Equiv.Perm (Fin n)) {C : Submodule K (Fin n → K)}
    (hC : paperSelfDualCode (K := K) C) :
    paperSelfDualCode (K := K) (permutedCode (K := K) σ C) := by
  have hCharacterization :=
    (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
      (K := K) (C := C)).mp hC
  apply (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
    (K := K) (C := permutedCode (K := K) σ C)).mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    change ∀ y ∈ permutedCode (K := K) σ C, dot y x = 0
    rcases hx with ⟨x₀, hx₀, rfl⟩
    intro y hy
    rcases hy with ⟨y₀, hy₀, rfl⟩
    change dot (permuteVec σ y₀) (permuteVec σ x₀) = 0
    rw [dot_coordinatePermuteLinearEquiv]
    exact hCharacterization.1 hx₀ y₀ hy₀
  · unfold permutedCode
    rw [(coordinatePermuteLinearEquiv (K := K) σ).finrank_map_eq]
    exact hCharacterization.2

theorem codeEquiv_preserves_paperSelfDualCode
    {m₁ m₂ n : ℕ} {R : Fin m₁ → Fin n → K} {S : Fin m₂ → Fin n → K}
    (hRS : CodeEquiv R S)
    (hR : paperSelfDualCode (K := K) (rowSpace R)) :
    paperSelfDualCode (K := K) (rowSpace S) := by
  rcases hRS with ⟨σ, hRS⟩
  change rowSpace (permuteFamily σ R) = rowSpace S at hRS
  rw [← hRS, rowSpace_permuteFamily_eq_permutedCode]
  exact paperSelfDualCode_permutedCode σ hR

end BuildingUpFormalization.Components.PermutationEquivalence
