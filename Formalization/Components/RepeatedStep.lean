import Formalization.Components.RepeatedStepDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RepeatedStep

open BuildingUpFormalization.Components.Foundations

variable {K : Type*} [Field K]

theorem rowSpace_topRowOperation {m n : ℕ} (a : K) (ha : a ≠ 0)
    (z : Fin m → K) (B : Matrix (Fin (m + 1)) (Fin n) K) :
    rowSpace (topRowOperation a z B) = rowSpace B := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · exact (rowSpace B).add_mem ((rowSpace B).smul_mem _ (mem_rowSpace B 0))
        (Submodule.sum_mem _ (fun i _ => (rowSpace B).smul_mem _ (mem_rowSpace B i.succ)))
    · exact mem_rowSpace B i.succ
  · have htail (i : Fin m) : B i.succ ∈ rowSpace (topRowOperation a z B) :=
      mem_rowSpace (topRowOperation a z B) i.succ
    have htop : a • B 0 ∈ rowSpace (topRowOperation a z B) := by
      have hsum : (∑ i, z i • B i.succ) ∈ rowSpace (topRowOperation a z B) :=
        Submodule.sum_mem _ (fun i _ =>
          (rowSpace (topRowOperation a z B)).smul_mem (z i) (htail i))
      have h := (rowSpace (topRowOperation a z B)).sub_mem
        (mem_rowSpace (topRowOperation a z B) 0)
        hsum
      simpa [topRowOperation] using h
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun i => htail i) i
    simpa [smul_smul, ha] using
      (rowSpace (topRowOperation a z B)).smul_mem a⁻¹ htop

private theorem c_ne_zero (c : K) (hc : c ^ 2 = (-1 : K)) : c ≠ 0 := by
  intro h
  simp [h] at hc

private theorem row_orthogonal {m n : ℕ} (B : Matrix (Fin m) (Fin n) K)
    (hB : paperSelfDualCode (rowSpace B)) (i j : Fin m) : dot (B i) (B j) = 0 :=
  ((pairwiseOrthogonal_iff_rowSpace_le_orthogonal (K := K)).2 hB.le) i j

theorem bordered_gram_exact {m n : ℕ} (c p : K) (rho : Fin n → K)
    (gamma : Fin m → K) (G : Matrix (Fin m) (Fin n) K)
    (hc : c ^ 2 = (-1 : K))
    (hB : paperSelfDualCode (rowSpace (borderedRows c p rho gamma G))) :
    dot rho rho = -1 - 2 * c * p ∧ ∀ i, dot rho (G i) = -c * gamma i := by
  constructor
  · have h := row_orthogonal _ hB 0 0
    simp only [borderedRows, Fin.cons_zero, dot_prepend2_prepend2] at h
    linear_combination h - p ^ 2 * hc
  · intro i
    have h := row_orthogonal _ hB 0 i.succ
    simp only [borderedRows, Fin.cons_zero, Fin.cons_succ, dot_prepend2_prepend2] at h
    linear_combination h - p * gamma i * hc

theorem one_step_normalization_exact {m n : ℕ} (c p : K) (rho : Fin n → K)
    (gamma : Fin m → K) (G : Matrix (Fin m) (Fin n) K)
    (hc : c ^ 2 = (-1 : K))
    (hG : paperSelfDualCode (rowSpace G))
    (hB : paperSelfDualCode (rowSpace (borderedRows c p rho gamma G)))
    (s : Fin m) (hs : gamma s ≠ 0) :
    let x := normalizedTail c p rho gamma G s
    dot x x = -1 ∧ (∀ i, dot x (G i) = -gamma i) ∧
    normalizedBorder c p rho gamma G s = buildRows x c G ∧
    rowSpace (borderedRows c p rho gamma G) = rowSpace (buildRows x c G) ∧
    (∀ i j, buildRows x c G i.succ (Fin.natAdd 2 j) = G i j) := by
  classical
  dsimp only
  have hc0 := c_ne_zero c hc
  have hcross := (bordered_gram_exact c p rho gamma G hc hB).2
  have hcoeff (i) : dot (normalizedTail c p rho gamma G s) (G i) = -gamma i := by
    rw [normalizedTail, dot_smul_left, dot_add_left, dot_smul_left,
      row_orthogonal G hG s i, hcross i]
    field_simp [hc0]
    ring
  have hhead : p + normalizingCoeff c p gamma s * gamma s = c := by
    simp [normalizingCoeff, hs]
  have htop : normalizedBorder c p rho gamma G s 0 =
      prepend2 1 0 (normalizedTail c p rho gamma G s) := by
    ext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      fin_cases i <;>
        simp [normalizedBorder, topRowOperation, borderedRows, Pi.single_apply,
          prepend2, head2, Finset.sum_ite_eq']
      · calc
          _ = c⁻¹ * (p + normalizingCoeff c p gamma s * gamma s) := by ring
          _ = 1 := by rw [hhead]; simp [hc0]
      · have hh : c * p + 1 + normalizingCoeff c p gamma s * (c * gamma s) = 0 := by
          calc
            _ = c * (p + normalizingCoeff c p gamma s * gamma s) + 1 := by ring
            _ = 0 := by rw [hhead, ← pow_two, hc]; ring
        calc
          _ = c⁻¹ * (c * p + 1 + normalizingCoeff c p gamma s * (c * gamma s)) := by ring
          _ = 0 := by rw [hh]; ring
    · intro j
      simp [normalizedBorder, topRowOperation, borderedRows, Pi.single_apply,
        prepend2, normalizedTail, Finset.sum_ite_eq', mul_assoc]
  have heq : normalizedBorder c p rho gamma G s =
      buildRows (normalizedTail c p rho gamma G s) c G := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · exact congrFun htop j
    · simp [normalizedBorder, topRowOperation, borderedRows, buildRows, ri, hcoeff]
  have hspace := rowSpace_topRowOperation c⁻¹ (inv_ne_zero hc0)
    (Pi.single s (c⁻¹ * normalizingCoeff c p gamma s)) (borderedRows c p rho gamma G)
  change rowSpace (normalizedBorder c p rho gamma G s) = _ at hspace
  have hnorm : dot (normalizedTail c p rho gamma G s)
      (normalizedTail c p rho gamma G s) = -1 := by
    have hm : normalizedBorder c p rho gamma G s 0 ∈
        rowSpace (borderedRows c p rho gamma G) := by
      rw [← hspace]
      exact mem_rowSpace _ 0
    have hz := hB.le hm _ hm
    change dot _ _ = 0 at hz
    rw [htop, dot_prepend2_prepend2] at hz
    linear_combination hz
  refine ⟨hnorm, hcoeff, heq, ?_, ?_⟩
  · simpa [heq] using hspace.symm
  · intro i j
    simp [buildRows, ri, prepend2]

theorem mem_of_dot_rows_zero {m n : ℕ} (G : Matrix (Fin m) (Fin n) K)
    (hG : paperSelfDualCode (rowSpace G)) (v : Fin n → K)
    (hv : ∀ i, dot v (G i) = 0) : v ∈ rowSpace G := by
  rw [hG]
  intro w hw
  change dot w v = 0
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      simpa [dot_comm] using hv i
  | zero => simp [dot]
  | add x y hx hy ihx ihy => rw [dot_add_left, ihx, ihy]; ring
  | smul a x hx ih => rw [dot_smul_left, ih]; ring

theorem zero_column_exact {m n : ℕ} (c p : K) (rho : Fin n → K)
    (G : Matrix (Fin m) (Fin n) K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hG : paperSelfDualCode (rowSpace G))
    (hB : paperSelfDualCode (rowSpace (borderedRows c p rho 0 G))) :
    p = c / 2 ∧ rho ∈ rowSpace G ∧
    rowSpace (borderedRows c p rho 0 G) = rowSpace (directSumRows c G) ∧
    ∀ x, rowSpace (borderedRows c p rho 0 G) ≠ rowSpace (buildRows x c G) := by
  classical
  have hc0 := c_ne_zero c hc
  obtain ⟨hn, ho⟩ := bordered_gram_exact c p rho 0 G hc hB
  have hrho : rho ∈ rowSpace G :=
    mem_of_dot_rows_zero G hG rho (by simpa using ho)
  have hrhon : dot rho rho = 0 := hG.le hrho rho hrho
  have hp : p = c / 2 := by
    apply (eq_div_iff h2).mpr
    linear_combination -c * hn + c * hrhon + 2 * p * hc
  have hp0 : p ≠ 0 := by rw [hp]; exact div_ne_zero hc0 h2
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hrho
  have hzj (j) : ∑ i, z i * G i j = rho j := by
    simpa using congrFun hz j
  have heq : topRowOperation p⁻¹ (fun i => -(p⁻¹ * z i))
      (borderedRows c p rho 0 G) = directSumRows c G := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.addCases ?_ ?_ j
      · intro t
        fin_cases t <;>
          simp [topRowOperation, borderedRows, directSumRows, prepend2, head2, hp0]
        rw [hp]
        field_simp [hc0, h2]
        linear_combination 2 * hc
      · intro j
        simp [topRowOperation, borderedRows, directSumRows, prepend2,
          Finset.sum_neg_distrib, mul_assoc, ← Finset.mul_sum, hzj]
    · simp [topRowOperation, borderedRows, directSumRows]
  have hspace : rowSpace (borderedRows c p rho 0 G) = rowSpace (directSumRows c G) := by
    rw [← heq]
    exact (rowSpace_topRowOperation p⁻¹ (inv_ne_zero hp0) _ _).symm
  refine ⟨hp, hrho, hspace, ?_⟩
  intro x hx
  have hdx : r0 x ∈ rowSpace (directSumRows c G) := by
    rw [← hspace, hx]
    exact mem_rowSpace (buildRows x c G) 0
  have heqD : directSumRows c G = pivotPureTailRows 0 (-c) 0 G := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      simp [directSumRows, pivotPureTailRows, pivotResidualTails]
  rw [heqD] at hdx
  exact r0_not_mem_rowSpace_pivotPureTailRows (K := K) 0 x (-c) 0 G
    (by simpa using hc) hdx

theorem one_step_kim_lee_iff {m n : ℕ} (c p : K) (rho : Fin n → K)
    (gamma : Fin m → K) (G : Matrix (Fin m) (Fin n) K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hG : paperSelfDualCode (rowSpace G))
    (hB : paperSelfDualCode (rowSpace (borderedRows c p rho gamma G))) :
    (∃ x, dot x x = -1 ∧
      rowSpace (borderedRows c p rho gamma G) = rowSpace (buildRows x c G)) ↔
      gamma ≠ 0 := by
  classical
  constructor
  · rintro ⟨x, _, hx⟩ hzero
    subst gamma
    exact (zero_column_exact c p rho G hc h2 hG hB).2.2.2 x hx
  · intro hg
    have hs : ∃ s, gamma s ≠ 0 := by
      by_contra! h
      exact hg (funext h)
    obtain ⟨s, hs⟩ := hs
    have h := one_step_normalization_exact c p rho gamma G hc hG hB s hs
    exact ⟨normalizedTail c p rho gamma G s, h.1, h.2.2.2.1⟩

theorem binary_normalization_exact {m n : ℕ} [CharP K 2]
    (rho : Fin n → K) (gamma : Fin m → K) (G : Matrix (Fin m) (Fin n) K)
    (hG : paperSelfDualCode (rowSpace G))
    (hB : paperSelfDualCode (rowSpace (borderedRows 1 0 rho gamma G)))
    (s : Fin m) (hs : gamma s = 1) :
    normalizedTail 1 0 rho gamma G s = rho + G s ∧
    normalizedBorder 1 0 rho gamma G s = buildRowsBin (rho + G s) G ∧
    dot (rho + G s) (rho + G s) = 1 ∧
    rowSpace (borderedRows 1 0 rho gamma G) = rowSpace (buildRowsBin (rho + G s) G) := by
  have hneg : (-1 : K) = 1 := by
    have htwo := CharP.cast_eq_zero K 2
    linear_combination -htwo
  have heq : normalizedTail 1 0 rho gamma G s = rho + G s := by
    simp [normalizedTail, normalizingCoeff, hs]
  have h := one_step_normalization_exact 1 0 rho gamma G
    (by simp [hneg]) hG hB s (by rw [hs]; exact one_ne_zero)
  have hb : buildRows (rho + G s) 1 G = buildRowsBin (rho + G s) G := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      simp [buildRows, buildRowsBin, ri, riBin,
        show ∀ a : K, -a = a from fun a => by linear_combination a * hneg]
  dsimp only at h
  rw [heq, hb, hneg] at h
  exact ⟨heq, h.2.2.1, h.1, h.2.2.2.1⟩

end BuildingUpFormalization.Components.RepeatedStep
