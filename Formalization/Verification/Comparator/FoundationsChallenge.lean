import Formalization.Components.FoundationsDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.Foundations

open LinearMap
open Module

section PlaneForms

variable {K : Type*} [Field K]

@[simp] theorem standardEuclideanPlaneForm_apply (u v : Plane K) :
    standardEuclideanPlaneForm u v = dot u v := by
  sorry

@[simp] theorem alternatingHyperbolicPlaneForm_apply (u v : Plane K) :
    alternatingHyperbolicPlaneForm u v = u 0 * v 1 + u 1 * v 0 := by
  sorry

theorem standardEuclideanPlaneForm_gram :
    standardEuclideanPlaneForm (K := K) planeE0 planeE0 = 1 ∧
    standardEuclideanPlaneForm (K := K) planeE0 planeE1 = 0 ∧
    standardEuclideanPlaneForm (K := K) planeE1 planeE0 = 0 ∧
    standardEuclideanPlaneForm (K := K) planeE1 planeE1 = 1 := by
  sorry

theorem alternatingHyperbolicPlaneForm_gram :
    alternatingHyperbolicPlaneForm (K := K) planeE0 planeE0 = 0 ∧
    alternatingHyperbolicPlaneForm (K := K) planeE0 planeE1 = 1 ∧
    alternatingHyperbolicPlaneForm (K := K) planeE1 planeE0 = 1 ∧
    alternatingHyperbolicPlaneForm (K := K) planeE1 planeE1 = 0 := by
  sorry

theorem standardEuclideanPlaneForm_not_isAlt :
    ¬(standardEuclideanPlaneForm (K := K)).IsAlt := by
  sorry

theorem alternatingHyperbolicPlaneForm_isAlt [CharP K 2] :
    (alternatingHyperbolicPlaneForm (K := K)).IsAlt := by
  sorry

theorem isAlt_of_isFormIsometry
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {Bᵥ : LinearMap.BilinForm K V} {B𝓌 : LinearMap.BilinForm K W}
    {e : V ≃ₗ[K] W}
    (he : IsFormIsometry Bᵥ B𝓌 e) (hAlt : B𝓌.IsAlt) : Bᵥ.IsAlt := by
  sorry

theorem no_isometry_standardEuclideanPlane_alternatingHyperbolicPlane [CharP K 2] :
    ¬∃ e : Plane K ≃ₗ[K] Plane K,
      IsFormIsometry standardEuclideanPlaneForm alternatingHyperbolicPlaneForm e := by
  sorry

end PlaneForms

section LagrangianDefinitions

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem selfOrthogonal_isTotallyIsotropic
    {B : LinearMap.BilinForm K V} {L : Submodule K V}
    (hL : IsSelfOrthogonal B L) : IsTotallyIsotropic B L := by
  sorry

theorem selfOrthogonal_isMaximalTotallyIsotropic
    {B : LinearMap.BilinForm K V} {L : Submodule K V}
    (hL : IsSelfOrthogonal B L) : IsMaximalTotallyIsotropic B L := by
  sorry

variable [FiniteDimensional K V]

theorem selfOrthogonal_iff_totallyIsotropic_and_finrank_half
    {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    {L : Submodule K V} :
    IsSelfOrthogonal B L ↔
      IsTotallyIsotropic B L ∧ 2 * finrank K L = finrank K V := by
  sorry

theorem selfOrthogonal_even_finrank
    {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    {L : Submodule K V} (hL : IsSelfOrthogonal B L) :
    Even (finrank K V) := by
  sorry

theorem selfOrthogonal_iff_maximalTotallyIsotropic_and_finrank_half
    {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    {L : Submodule K V} :
    IsSelfOrthogonal B L ↔
      IsMaximalTotallyIsotropic B L ∧ 2 * finrank K L = finrank K V := by
  sorry

theorem paperLagrangianSubspace_iff_totallyIsotropic_and_finrank_half
    {n : ℕ} {L : Submodule K (Fin n → K)} :
    paperLagrangianSubspace (K := K) L ↔
      IsTotallyIsotropic (dotBilin (K := K) (n := n)) L ∧
        2 * finrank K L = finrank K (Fin n → K) := by
  sorry

theorem paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
    {n : ℕ} {C : Submodule K (Fin n → K)} :
    paperSelfDualCode (K := K) C ↔
      IsTotallyIsotropic (dotBilin (K := K) (n := n)) C ∧
        2 * finrank K C = finrank K (Fin n → K) := by
  sorry

theorem paperLagrangianSubspace_even_length
    {n : ℕ} {L : Submodule K (Fin n → K)}
    (hL : paperLagrangianSubspace (K := K) L) :
    Even n := by
  sorry

theorem paperSelfDualCode_even_length
    {n : ℕ} {C : Submodule K (Fin n → K)}
    (hC : paperSelfDualCode (K := K) C) :
    Even n := by
  sorry

end LagrangianDefinitions

section SystematicForm

variable {K : Type*} [Field K]

theorem systematicRows_linearIndependent
    {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    LinearIndependent K (systematicRows A) := by
  sorry

theorem dot_systematicRows
    {k : ℕ} (A : Matrix (Fin k) (Fin k) K) (i j : Fin k) :
    dot (systematicRows A i) (systematicRows A j) =
      (1 : Matrix (Fin k) (Fin k) K) i j +
        (A * A.transpose) i j := by
  sorry

theorem systematicRows_pairwiseOrthogonal_iff
    {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    PairwiseOrthogonal (K := K) (systematicRows A) ↔
      A * A.transpose = -(1 : Matrix (Fin k) (Fin k) K) := by
  sorry

theorem systematicRows_selfDual_iff_pairwiseOrthogonal
    {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    paperSelfDualCode (K := K) (rowSpace (systematicRows A)) ↔
      PairwiseOrthogonal (K := K) (systematicRows A) := by
  sorry

theorem paper_systematic_form_criterion_exact
    {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    paperSelfDualCode (K := K) (rowSpace (systematicRows A)) ↔
      A * A.transpose = -(1 : Matrix (Fin k) (Fin k) K) := by
  sorry

end SystematicForm

end BuildingUpFormalization.Components.Foundations
