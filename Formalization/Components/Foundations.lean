import Formalization.Components.FoundationsDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.Foundations

open LinearMap
open Module

section PlaneForms

variable {K : Type*} [Field K]

@[simp] theorem standardEuclideanPlaneForm_apply (u v : Plane K) :
    standardEuclideanPlaneForm u v = dot u v := by
  rfl

@[simp] theorem alternatingHyperbolicPlaneForm_apply (u v : Plane K) :
    alternatingHyperbolicPlaneForm u v = u 0 * v 1 + u 1 * v 0 := by
  rfl

theorem standardEuclideanPlaneForm_gram :
    standardEuclideanPlaneForm (K := K) planeE0 planeE0 = 1 ∧
    standardEuclideanPlaneForm (K := K) planeE0 planeE1 = 0 ∧
    standardEuclideanPlaneForm (K := K) planeE1 planeE0 = 0 ∧
    standardEuclideanPlaneForm (K := K) planeE1 planeE1 = 1 := by
  simp [standardEuclideanPlaneForm, planeE0, planeE1, dotBilin, dot, Pi.single_apply]

theorem alternatingHyperbolicPlaneForm_gram :
    alternatingHyperbolicPlaneForm (K := K) planeE0 planeE0 = 0 ∧
    alternatingHyperbolicPlaneForm (K := K) planeE0 planeE1 = 1 ∧
    alternatingHyperbolicPlaneForm (K := K) planeE1 planeE0 = 1 ∧
    alternatingHyperbolicPlaneForm (K := K) planeE1 planeE1 = 0 := by
  simp [planeE0, planeE1]

theorem standardEuclideanPlaneForm_not_isAlt :
    ¬(standardEuclideanPlaneForm (K := K)).IsAlt := by
  intro hAlt
  have hzero := hAlt.self_eq_zero (planeE0 (K := K))
  simp [standardEuclideanPlaneForm, planeE0, dotBilin, dot, Pi.single_apply] at hzero

theorem alternatingHyperbolicPlaneForm_isAlt [CharP K 2] :
    (alternatingHyperbolicPlaneForm (K := K)).IsAlt := by
  intro u
  rw [alternatingHyperbolicPlaneForm_apply]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  calc
    u 0 * u 1 + u 1 * u 0 = 2 * (u 0 * u 1) := by ring
    _ = 0 := by rw [htwo, zero_mul]

theorem isAlt_of_isFormIsometry
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {Bᵥ : LinearMap.BilinForm K V} {B𝓌 : LinearMap.BilinForm K W}
    {e : V ≃ₗ[K] W}
    (he : IsFormIsometry Bᵥ B𝓌 e) (hAlt : B𝓌.IsAlt) : Bᵥ.IsAlt := by
  intro x
  rw [← he x x]
  exact hAlt.self_eq_zero (e x)

theorem no_isometry_standardEuclideanPlane_alternatingHyperbolicPlane [CharP K 2] :
    ¬∃ e : Plane K ≃ₗ[K] Plane K,
      IsFormIsometry standardEuclideanPlaneForm alternatingHyperbolicPlaneForm e := by
  rintro ⟨e, he⟩
  exact standardEuclideanPlaneForm_not_isAlt
    (isAlt_of_isFormIsometry he alternatingHyperbolicPlaneForm_isAlt)

end PlaneForms

section LagrangianDefinitions

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem selfOrthogonal_isTotallyIsotropic
    {B : LinearMap.BilinForm K V} {L : Submodule K V}
    (hL : IsSelfOrthogonal B L) : IsTotallyIsotropic B L := by
  exact hL.le

theorem selfOrthogonal_isMaximalTotallyIsotropic
    {B : LinearMap.BilinForm K V} {L : Submodule K V}
    (hL : IsSelfOrthogonal B L) : IsMaximalTotallyIsotropic B L := by
  refine ⟨selfOrthogonal_isTotallyIsotropic hL, ?_⟩
  intro M hM hLM
  apply le_antisymm
  · calc
      M ≤ B.orthogonal M := hM
      _ ≤ B.orthogonal L := B.orthogonal_le hLM
      _ = L := hL.symm
  · exact hLM

variable [FiniteDimensional K V]

theorem selfOrthogonal_iff_totallyIsotropic_and_finrank_half
    {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    {L : Submodule K V} :
    IsSelfOrthogonal B L ↔
      IsTotallyIsotropic B L ∧ 2 * finrank K L = finrank K V := by
  constructor
  · intro hL
    refine ⟨selfOrthogonal_isTotallyIsotropic hL, ?_⟩
    have hrank := LinearMap.BilinForm.finrank_orthogonal hB L
    rw [← hL] at hrank
    have hle : finrank K L ≤ finrank K V := Submodule.finrank_le L
    omega
  · rintro ⟨hIso, hHalf⟩
    apply Submodule.eq_of_le_of_finrank_eq hIso
    rw [LinearMap.BilinForm.finrank_orthogonal hB]
    have hle : finrank K L ≤ finrank K V := Submodule.finrank_le L
    omega

theorem selfOrthogonal_even_finrank
    {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    {L : Submodule K V} (hL : IsSelfOrthogonal B L) :
    Even (finrank K V) := by
  have hHalf :=
    (selfOrthogonal_iff_totallyIsotropic_and_finrank_half hB).mp hL |>.2
  exact ⟨finrank K L, by omega⟩

theorem selfOrthogonal_iff_maximalTotallyIsotropic_and_finrank_half
    {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    {L : Submodule K V} :
    IsSelfOrthogonal B L ↔
      IsMaximalTotallyIsotropic B L ∧ 2 * finrank K L = finrank K V := by
  constructor
  · intro hL
    have hCharacterization :=
      (selfOrthogonal_iff_totallyIsotropic_and_finrank_half hB).1 hL
    exact ⟨selfOrthogonal_isMaximalTotallyIsotropic hL, hCharacterization.2⟩
  · rintro ⟨hMaximal, hHalf⟩
    exact (selfOrthogonal_iff_totallyIsotropic_and_finrank_half hB).2
      ⟨hMaximal.1, hHalf⟩

theorem paperLagrangianSubspace_iff_totallyIsotropic_and_finrank_half
    {n : ℕ} {L : Submodule K (Fin n → K)} :
    paperLagrangianSubspace (K := K) L ↔
      IsTotallyIsotropic (dotBilin (K := K) (n := n)) L ∧
        2 * finrank K L = finrank K (Fin n → K) := by
  exact selfOrthogonal_iff_totallyIsotropic_and_finrank_half
    (dotBilin_nondegenerate (K := K) (n := n))

theorem paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
    {n : ℕ} {C : Submodule K (Fin n → K)} :
    paperSelfDualCode (K := K) C ↔
      IsTotallyIsotropic (dotBilin (K := K) (n := n)) C ∧
        2 * finrank K C = finrank K (Fin n → K) := by
  simpa [paperSelfDualCode, paperLagrangianSubspace] using
    (paperLagrangianSubspace_iff_totallyIsotropic_and_finrank_half
      (K := K) (L := C))

theorem paperLagrangianSubspace_even_length
    {n : ℕ} {L : Submodule K (Fin n → K)}
    (hL : paperLagrangianSubspace (K := K) L) :
    Even n := by
  simpa using selfOrthogonal_even_finrank
    (dotBilin_nondegenerate (K := K) (n := n)) hL

theorem paperSelfDualCode_even_length
    {n : ℕ} {C : Submodule K (Fin n → K)}
    (hC : paperSelfDualCode (K := K) C) :
    Even n := by
  exact paperLagrangianSubspace_even_length
    ((paper_self_dual_iff_lagrangian (K := K) (C := C)).mp hC)

end LagrangianDefinitions

section SystematicForm

variable {K : Type*} [Field K]

theorem systematicRows_linearIndependent
    {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    LinearIndependent K (systematicRows A) := by
  classical
  refine Fintype.linearIndependent_iff.mpr ?_
  intro g hg i
  have hi := congrFun hg (Fin.castAdd k i)
  simpa [systematicRows, Pi.single_apply, eq_comm] using hi

theorem dot_systematicRows
    {k : ℕ} (A : Matrix (Fin k) (Fin k) K) (i j : Fin k) :
    dot (systematicRows A i) (systematicRows A j) =
      (1 : Matrix (Fin k) (Fin k) K) i j +
        (A * A.transpose) i j := by
  classical
  simp only [systematicRows]
  rw [dot_append_append]
  simp [dot, Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem systematicRows_pairwiseOrthogonal_iff
    {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    PairwiseOrthogonal (K := K) (systematicRows A) ↔
      A * A.transpose = -(1 : Matrix (Fin k) (Fin k) K) := by
  constructor
  · intro horth
    ext i j
    have hij := horth i j
    rw [dot_systematicRows] at hij
    have hone : (1 : Matrix (Fin k) (Fin k) K) i j +
        (A * A.transpose) i j = 0 := hij
    change (A * A.transpose) i j =
      -((1 : Matrix (Fin k) (Fin k) K) i j)
    linear_combination hone
  · intro hmatrix i j
    rw [dot_systematicRows]
    have hij := congrFun (congrFun hmatrix i) j
    simpa using congrArg
      (fun z : K => (1 : Matrix (Fin k) (Fin k) K) i j + z) hij

theorem systematicRows_selfDual_iff_pairwiseOrthogonal
    {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    paperSelfDualCode (K := K) (rowSpace (systematicRows A)) ↔
      PairwiseOrthogonal (K := K) (systematicRows A) := by
  constructor
  · intro hself
    exact (pairwiseOrthogonal_iff_rowSpace_le_orthogonal (K := K)).2 hself.le
  · intro horth
    apply (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
      (K := K) (C := rowSpace (systematicRows A))).2
    constructor
    · exact rowSpace_le_orthogonal_of_pairwiseOrthogonal horth
    · have hlin := systematicRows_linearIndependent A
      rw [show Module.finrank K ↥(rowSpace (systematicRows A)) = k by
          simpa [rowSpace] using finrank_span_eq_card hlin,
        Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      omega

/-- Exact paper-facing form of the systematic generator criterion. -/
theorem paper_systematic_form_criterion_exact
    {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    paperSelfDualCode (K := K) (rowSpace (systematicRows A)) ↔
      A * A.transpose = -(1 : Matrix (Fin k) (Fin k) K) := by
  rw [systematicRows_selfDual_iff_pairwiseOrthogonal,
    systematicRows_pairwiseOrthogonal_iff]

end SystematicForm

end BuildingUpFormalization.Components.Foundations
