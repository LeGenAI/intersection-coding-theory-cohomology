import Formalization.Components.BinaryCzKimDefinitions
import Formalization.Components.Foundations

set_option autoImplicit false

namespace BuildingUpFormalization.Components.BinaryCzKim

open BuildingUpFormalization.Components.Foundations
open LinearMap
open Module

variable {K : Type*} [Field K]

@[simp] theorem binaryDiagonalHead_apply_zero :
    binaryDiagonalHead (K := K) 0 = 1 := by
  simp [binaryDiagonalHead, planeE0, planeE1]

@[simp] theorem binaryDiagonalHead_apply_one :
    binaryDiagonalHead (K := K) 1 = 1 := by
  simp [binaryDiagonalHead, planeE0, planeE1]

theorem standardEuclideanPlaneForm_binaryDiagonalHead_self [CharP K 2] :
    standardEuclideanPlaneForm (K := K) binaryDiagonalHead binaryDiagonalHead = 0 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [standardEuclideanPlaneForm_apply]
  simp only [dot, Fin.sum_univ_two, binaryDiagonalHead_apply_zero,
    binaryDiagonalHead_apply_one, mul_one]
  simpa [one_add_one_eq_two] using htwo

theorem standardEuclideanPlaneForm_planeE0_binaryDiagonalHead :
    standardEuclideanPlaneForm (K := K) planeE0 binaryDiagonalHead = 1 := by
  rw [standardEuclideanPlaneForm_apply]
  simp [dot, planeE0, planeE1, binaryDiagonalHead,
    Pi.single_apply]

theorem standardEuclideanPlane_head_not_hyperbolicPair :
    ¬paperHyperbolicPair (K := K) planeE0 binaryDiagonalHead := by
  intro h
  have hzero := h.1
  simp [dot, planeE0, Pi.single_apply] at hzero

theorem dot_r0_riBin_eq_zero_iff [CharP K 2]
    {n : ℕ} (x g : Fin n → K) (y : K) :
    dot (r0 x) (riBin y g) = 0 ↔ y = dot x g := by
  rw [r0, riBin, dot_prepend2_prepend2]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hneg (a : K) : -a = a := by
    apply neg_eq_iff_add_eq_zero.mpr
    calc
      a + a = 2 * a := by ring
      _ = 0 := by rw [htwo, zero_mul]
  simp only [one_mul, zero_mul]
  rw [add_eq_zero_iff_eq_neg, hneg]
  simp

theorem boxedFamily_coefficient_eq_dot [CharP K 2]
    {m n : ℕ} {x : Fin n → K} {Y : Fin m → K} {G : Fin m → Fin n → K}
    (horth : PairwiseOrthogonal (K := K) (boxedFamily x Y G)) :
    ∀ i : Fin m, Y i = dot x (G i) := by
  intro i
  have h := horth 0 (Fin.succ i)
  simpa only [boxedFamily, Fin.cases_zero, Fin.cases_succ,
    dot_r0_riBin_eq_zero_iff] using h

theorem dot_riBin_riBin_eq_dot [CharP K 2]
    {n : ℕ} (g h : Fin n → K) (y z : K) :
    dot (riBin y g) (riBin z h) = dot g h := by
  rw [riBin, riBin, dot_prepend2_prepend2]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  calc
    y * z + y * z + dot g h = 2 * (y * z) + dot g h := by ring
    _ = dot g h := by rw [htwo, zero_mul, zero_add]

theorem boxedFamily_tail_pairwiseOrthogonal [CharP K 2]
    {m n : ℕ} {x : Fin n → K} {Y : Fin m → K} {G : Fin m → Fin n → K}
    (horth : PairwiseOrthogonal (K := K) (boxedFamily x Y G)) :
    PairwiseOrthogonal (K := K) G := by
  intro i j
  have hij := horth (Fin.succ i) (Fin.succ j)
  simpa only [boxedFamily, Fin.cases_succ, dot_riBin_riBin_eq_dot] using hij

@[simp] theorem buildSuccBinLinear_apply
    {n : ℕ} (x g : Fin n → K) :
    buildSuccBinLinear x g = riBin (dot x g) g := by
  rfl

theorem buildRowsBin_succ_eq_buildSuccBinLinear
    {m n : ℕ} (x : Fin n → K) (G : Fin m → Fin n → K) (i : Fin m) :
    buildRowsBin x G (Fin.succ i) = buildSuccBinLinear x (G i) := by
  rfl

theorem buildRowsBin_tail_linearIndependent
    {m n : ℕ} {x : Fin n → K} {G : Fin m → Fin n → K}
    (hbuild : LinearIndependent K (buildRowsBin x G)) :
    LinearIndependent K G := by
  have hsucc :
      LinearIndependent K (fun i : Fin m ↦ buildRowsBin x G (Fin.succ i)) := by
    simpa only [Function.comp_apply] using
      hbuild.comp Fin.succ (Fin.succ_injective m)
  have himage : LinearIndependent K (buildSuccBinLinear x ∘ G) := by
    simpa only [Function.comp_apply, buildRowsBin_succ_eq_buildSuccBinLinear] using hsucc
  exact LinearIndependent.of_comp (buildSuccBinLinear x) himage

theorem buildRows_one_eq_buildRowsBin [CharP K 2]
    {m n : ℕ} (x : Fin n → K) (G : Fin m → Fin n → K) :
    buildRows x 1 G = buildRowsBin x G := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [buildRows, buildRowsBin]
  · have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hneg (a : K) : -a = a := by
      apply neg_eq_iff_add_eq_zero.mpr
      calc
        a + a = 2 * a := by ring
        _ = 0 := by rw [htwo, zero_mul]
    simp [buildRows, buildRowsBin, ri, riBin, hneg]

/-- Exact paper-facing form of Kim's binary building-up theorem. -/
theorem paper_binary_kim_building_up_exact [CharP K 2]
    {m : ℕ} {x : Fin (2 * m) → K}
    {G : Fin m → Fin (2 * m) → K}
    (hx : dot x x = (1 : K))
    (hparent : paperSelfDualCode (K := K) (rowSpace G)) :
    paperSelfDualCode (K := K) (rowSpace (buildRowsBin x G)) := by
  have horth : PairwiseOrthogonal (K := K) G :=
    (pairwiseOrthogonal_iff_rowSpace_le_orthogonal (K := K)).2 hparent.le
  have hhalf :=
    (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
      (K := K) (C := rowSpace G)).mp hparent |>.2
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hhalf
  have hdim : Module.finrank K ↥(rowSpace G) = m := by omega
  have hlin : LinearIndependent K G := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simpa [rowSpace] using hdim.symm
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hneg_one : (-1 : K) = 1 := by
    apply neg_eq_iff_add_eq_zero.mpr
    simpa [one_add_one_eq_two] using htwo
  have hx' : dot x x = (-1 : K) := by simpa [hneg_one] using hx
  have hc : (1 : K) ^ 2 = (-1 : K) := by simp [hneg_one]
  have hgeneral : paperSelfDualCode (K := K) (rowSpace (buildRows x 1 G)) := by
    exact buildRows_rowSpace_self_dual_of_self_dual_parent_basis
      (K := K) (hx := hx') (hc := hc) (hGorth := horth)
      (hGlin := hlin) (heven := ⟨m, by omega⟩) (hcard := by omega)
  rwa [buildRows_one_eq_buildRowsBin] at hgeneral

theorem isSelfOrthogonal_map_of_isFormIsometry
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {Bᵥ : LinearMap.BilinForm K V} {B𝓌 : LinearMap.BilinForm K W}
    {e : V ≃ₗ[K] W} {L : Submodule K V}
    (he : IsFormIsometry Bᵥ B𝓌 e) (hL : IsSelfOrthogonal Bᵥ L) :
    IsSelfOrthogonal B𝓌 (L.map e.toLinearMap) := by
  rw [IsSelfOrthogonal] at hL ⊢
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    apply (LinearMap.BilinForm.mem_orthogonal_iff).2
    intro _ hw
    rcases hw with ⟨u, hu, rfl⟩
    rw [LinearMap.BilinForm.isOrtho_def]
    change B𝓌 (e u) (e v) = 0
    rw [he u v]
    have hvOrth : v ∈ Bᵥ.orthogonal L := hL ▸ hv
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hvOrth) u hu
  · intro w hw
    refine ⟨e.symm w, ?_, by simp⟩
    rw [hL]
    apply (LinearMap.BilinForm.mem_orthogonal_iff).2
    intro u hu
    have heu : e u ∈ L.map e.toLinearMap := ⟨u, hu, rfl⟩
    have hwu := (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) (e u) heu
    rw [LinearMap.BilinForm.isOrtho_def] at hwu ⊢
    calc
      Bᵥ u (e.symm w) = B𝓌 (e u) (e (e.symm w)) := (he u (e.symm w)).symm
      _ = B𝓌 (e u) w := by simp
      _ = 0 := hwu

theorem boxedFamily_linearIndependent_of_paperSelfDualCode
    {m : ℕ} {x : Fin (2 * m) → K} {Y : Fin m → K}
    {G : Fin m → Fin (2 * m) → K}
    (hself : paperSelfDualCode (K := K) (rowSpace (boxedFamily x Y G))) :
    LinearIndependent K (boxedFamily x Y G) := by
  have hhalf :=
    (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
      (K := K) (C := rowSpace (boxedFamily x Y G))).mp hself |>.2
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hhalf
  have hdim : Module.finrank K ↥(rowSpace (boxedFamily x Y G)) = m + 1 := by
    omega
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  simpa [rowSpace] using hdim.symm

theorem boxedFamily_tail_paperSelfDualCode [CharP K 2]
    {m : ℕ} {x : Fin (2 * m) → K} {Y : Fin m → K}
    {G : Fin m → Fin (2 * m) → K}
    (hself : paperSelfDualCode (K := K) (rowSpace (boxedFamily x Y G))) :
    paperSelfDualCode (K := K) (rowSpace G) := by
  have horth : PairwiseOrthogonal (K := K) (boxedFamily x Y G) :=
    (pairwiseOrthogonal_iff_rowSpace_le_orthogonal (K := K)).2 hself.le
  have hY := boxedFamily_coefficient_eq_dot horth
  have heq : boxedFamily x Y G = buildRowsBin x G := boxedFamily_eq_buildRowsBin hY
  have hlinBuild : LinearIndependent K (buildRowsBin x G) := by
    rw [← heq]
    exact boxedFamily_linearIndependent_of_paperSelfDualCode hself
  have hlinG := buildRowsBin_tail_linearIndependent hlinBuild
  apply (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
    (K := K) (C := rowSpace G)).2
  refine ⟨?_, ?_⟩
  · exact rowSpace_le_orthogonal_of_pairwiseOrthogonal (K := K)
      (boxedFamily_tail_pairwiseOrthogonal horth)
  · rw [show Module.finrank K ↥(rowSpace G) = m by
        simpa [rowSpace] using finrank_span_eq_card hlinG,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- Correct paper-facing binary theorem.  It keeps the cohomological form and
the standard Euclidean form distinct, transports self-orthogonality through an
explicit isometry, and derives the Kim coefficients and parent code from the
boxed Euclidean representative. -/
theorem paper_binary_cz_kim_corrected [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module K V]
    {m : ℕ} {Bcoh : LinearMap.BilinForm K V} {L : Submodule K V}
    (e : V ≃ₗ[K] (Fin (2 + 2 * m) → K))
    (he : IsFormIsometry Bcoh (dotBilin (K := K) (n := 2 + 2 * m)) e)
    (hL : IsSelfOrthogonal Bcoh L)
    {x : Fin (2 * m) → K} {Y : Fin m → K}
    {G : Fin m → Fin (2 * m) → K}
    (hcode : L.map e.toLinearMap = rowSpace (boxedFamily x Y G)) :
    IsSelfOrthogonal (dotBilin (K := K) (n := 2 + 2 * m)) (L.map e.toLinearMap) ∧
      dot x x = (1 : K) ∧
      paperSelfDualCode (K := K) (rowSpace G) ∧
      (∀ i : Fin m, Y i = dot x (G i)) ∧
      boxedFamily x Y G = buildRowsBin x G ∧
      deleteBinaryHeadPair (boxedFamily x Y G) = G ∧
      CodeEquiv (buildRowsBin x (deleteBinaryHeadPair (boxedFamily x Y G)))
        (boxedFamily x Y G) := by
  have htransport := isSelfOrthogonal_map_of_isFormIsometry he hL
  have hselfBoxed : paperSelfDualCode (K := K) (rowSpace (boxedFamily x Y G)) := by
    simpa [paperSelfDualCode, IsSelfOrthogonal, hcode] using htransport
  have horth : PairwiseOrthogonal (K := K) (boxedFamily x Y G) :=
    (pairwiseOrthogonal_iff_rowSpace_le_orthogonal (K := K)).2 hselfBoxed.le
  have hx : dot x x = (1 : K) := by
    have hxx : dot (r0 x) (r0 x) = 0 := by
      simpa only [boxedFamily, Fin.cases_zero] using horth 0 0
    rw [r0, dot_prepend2_prepend2] at hxx
    have hneg : dot x x = (-1 : K) := by
      linear_combination hxx
    have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hnegOne : (-1 : K) = 1 := by
      apply neg_eq_iff_add_eq_zero.mpr
      simpa [one_add_one_eq_two] using htwo
    simpa [hnegOne] using hneg
  have hY : ∀ i : Fin m, Y i = dot x (G i) :=
    boxedFamily_coefficient_eq_dot horth
  have heq : boxedFamily x Y G = buildRowsBin x G := boxedFamily_eq_buildRowsBin hY
  have hdelete : deleteBinaryHeadPair (boxedFamily x Y G) = G := by
    rw [deleteBinaryHeadPair, heq]
    exact deleteHyperbolicPair_buildRowsBin x G
  refine ⟨htransport, hx, boxedFamily_tail_paperSelfDualCode hselfBoxed,
    hY, heq, hdelete, ?_⟩
  rw [hdelete, ← heq]
  exact codeEquiv_refl (boxedFamily x Y G)

end BuildingUpFormalization.Components.BinaryCzKim
