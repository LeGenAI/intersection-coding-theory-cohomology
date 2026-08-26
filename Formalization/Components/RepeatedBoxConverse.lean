import Formalization.Components.RepeatedBox

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RepeatedBox

open BuildingUpFormalization.Components.SplitBoxed
open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.RankBoxedStructure
open BuildingUpFormalization.Components.RankBoxedExtension
open BuildingUpFormalization.Components.RepeatedStep

variable {K : Type*} [Field K]

@[simp] theorem extensionTail_pivot {k r : ℕ} (c : K)
    (h q : Fin r → K) (u : Fin k → K) (j : Fin k) :
    extensionTail c h q u (.inl j) = isotropicLineBlock c (u j) := rfl

@[simp] theorem extensionTail_terminal {k r : ℕ} (c : K)
    (h q : Fin r → K) (u : Fin k → K) (t : Fin r) :
    extensionTail c h q u (.inr t) = splitAffineBlock c (h t) (q t) := rfl

theorem extensionTail_norm {k r : ℕ} (c : K) (hc : c * c = -1)
    (h q : Fin r → K) (u : Fin k → K) :
    rankBoxRowInner (extensionTail c h q u) (extensionTail c h q u) =
      2 * c * (∑ t, h t * q t) + ∑ t, q t * q t := by
  simp only [rankBoxRowInner, extensionTail_pivot, extensionTail_terminal]
  simp_rw [splitBlockInner_isotropic_isotropic _ _ _ hc,
    splitBlockInner_splitAffineBlock_of_sq_neg_one _ _ _ _ _ hc]
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem extensionTail_dot_pivot {k r : ℕ} (c : K) (hc : c * c = -1)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (h q : Fin r → K) (u : Fin k → K) (i : Fin k) :
    rankBoxRowInner (extensionTail c h q u) (rankBoxedRows c P H Q A D (.inl i)) =
      c * u i + c * (∑ t, (h t * Q i t + q t * H i t)) + ∑ t, q t * Q i t := by
  classical
  simp only [rankBoxRowInner, extensionTail_pivot, extensionTail_terminal, rankBoxedRows]
  simp_rw [splitBlockInner_isotropic_splitAffine _ _ _ _ hc,
    splitBlockInner_splitAffineBlock_of_sq_neg_one _ _ _ _ _ hc]
  simp [mul_ite, Finset.sum_add_distrib, ← Finset.mul_sum, add_assoc]

theorem extensionTail_dot_terminal {k r : ℕ} (c : K) (hc : c * c = -1)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (h q : Fin r → K) (u : Fin k → K) (s : Fin r) :
    rankBoxRowInner (extensionTail c h q u) (rankBoxedRows c P H Q A D (.inr s)) =
      c * ∑ t, q t * D s t := by
  simp only [rankBoxRowInner, extensionTail_pivot, extensionTail_terminal, rankBoxedRows]
  simp_rw [splitBlockInner_isotropic_isotropic _ _ _ hc,
    splitBlockInner_splitAffine_isotropic _ _ _ _ hc]
  simp [mul_assoc, ← Finset.mul_sum]

theorem extension_parameters_forced {k r : ℕ} (c p : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (h q : Fin r → K) (u : Fin k → K) (gamma : Fin (k + r) → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hB : paperSelfDualCode (rowSpace (borderedRows c p
      (flattenRow (extensionTail c h q u)) gamma
      (flattenRows (rankBoxedRows c P H Q A D))))) :
    p = c / 2 * (1 + ∑ t, q t * q t) - ∑ t, h t * q t ∧
    gamma = fun i => extensionGamma c H Q D h q u (finSumFinEquiv.symm i) := by
  have hcm : c * c = -1 := by simpa [pow_two] using hc
  obtain ⟨hn, ho⟩ := bordered_gram_exact c p _ gamma _ hc hB
  rw [flatten_dot, extensionTail_norm c hcm] at hn
  constructor
  · have hp2 : 2 * p = c * (1 + ∑ t, q t * q t) - 2 * ∑ t, h t * q t := by
      linear_combination -c * hn + 2 * ((∑ t, h t * q t) + p) * hc
    calc
      p = (2 * p) / 2 := by field_simp
      _ = c / 2 * (1 + ∑ t, q t * q t) - ∑ t, h t * q t := by
        rw [hp2]
        field_simp
  · funext i
    have hi := ho i
    simp only [flattenRows, flatten_dot] at hi
    cases he : finSumFinEquiv.symm i with
    | inl j =>
        rw [he, extensionTail_dot_pivot c hcm] at hi
        simp only [extensionGamma]
        linear_combination -c * hi +
          (u j + (∑ t, (h t * Q j t + q t * H j t)) + gamma i) * hc
    | inr s =>
        rw [he, extensionTail_dot_terminal c hcm] at hi
        simp only [extensionGamma]
        linear_combination -c * hi + ((∑ t, q t * D s t) + gamma i) * hc

theorem reverseTail_pivot_defect {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (x : Fin ((k + r) * 2) → K) (j : Fin k) :
    blockDefectLinear c (reverseTail c P H Q A D x (.inl j)) = 0 := by
  classical
  simp only [reverseTail, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
    map_sub, map_smul, map_sum, rankBoxedRows, blockDefectLinear_splitAffineBlock]
  simp [smul_eq_mul, mul_ite, eq_comm, blockDefectLinear]

theorem reverseTail_shape {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (x : Fin ((k + r) * 2) → K) :
    let rho := reverseTail c P H Q A D x
    rho = extensionTail c (fun t => rho (.inr t) 0)
      (fun t => blockDefect c (rho (.inr t))) (fun j => rho (.inl j) 0) := by
  dsimp only
  funext j b
  cases j with
  | inl j =>
      have hj := reverseTail_pivot_defect c P H Q A D x j
      change _ - c * _ = 0 at hj
      fin_cases b
      · rfl
      · exact sub_eq_zero.mp hj
  | inr t =>
      fin_cases b
      · rfl
      · simp [extensionTail, head2, blockDefect]

theorem kim_lee_top_to_border {m n : ℕ} (c : K) (z : Fin m → K)
    (x : Fin n → K) (G : Matrix (Fin m) (Fin n) K) (hc : c ^ 2 = (-1 : K)) :
    topRowOperation c z (buildRows x c G) =
      borderedRows c (c + ∑ i, z i * (-dot x (G i)))
        (c • x + ∑ i, z i • G i) (fun i => -dot x (G i)) G := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.addCases ?_ ?_ j
    · intro t
      fin_cases t
      · simp [topRowOperation, buildRows, r0, ri, borderedRows, prepend2, head2]
      · have hs : (∑ i, z i * (-(c * dot x (G i)))) =
            c * ∑ i, z i * (-dot x (G i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        simp only [topRowOperation, buildRows, Fin.cons_zero, Fin.cases_zero,
          Fin.cases_succ, r0, ri, borderedRows, prepend2, Fin.append_left,
          head2, Fin.cons_zero,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
        rw [hs]
        linear_combination -hc
    · intro j
      simp [topRowOperation, buildRows, r0, ri, borderedRows, prepend2]
  · simp [topRowOperation, buildRows, ri, borderedRows, prepend2]

theorem flatten_reverseTail {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (x : Fin ((k + r) * 2) → K) :
    c • x + ∑ i, reverseCoeff c x i • flattenRows (rankBoxedRows c P H Q A D) i =
      flattenRow (reverseTail c P H Q A D x) := by
  classical
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp only [reverseCoeff, Equiv.symm_apply_apply, zero_smul,
    Finset.sum_const_zero, add_zero, neg_smul, Finset.sum_neg_distrib]
  ext j
  simp only [flattenRows, flattenRow, reverseTail, unflattenRow,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
    Finset.sum_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply, Prod.mk.eta]
  ring

theorem kim_lee_gamma_ne_zero {m n : ℕ} (x : Fin n → K)
    (G : Matrix (Fin m) (Fin n) K) (hx : dot x x = -1)
    (hG : paperSelfDualCode (rowSpace G)) : (fun i => -dot x (G i)) ≠ 0 := by
  intro hz
  have hxmem : x ∈ rowSpace G := mem_of_dot_rows_zero G hG x (by
    intro i
    simpa using congrFun hz i)
  have hzero : dot x x = 0 := hG.le hxmem x hxmem
  rw [hx] at hzero
  exact neg_ne_zero.mpr one_ne_zero hzero

/-- Every norm-minus-one vector gives exactly a repeated successor after
the displayed top-row operation. All old rows, coordinates and D remain
fixed; the conclusion is not merely that two codes are self-dual. -/
theorem kim_lee_to_repeated_exact {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D) (hpp : PivotGramRelations c P H Q)
    (x : Fin ((k + r) * 2) → K) (hx : dot x x = -1) :
    let G := flattenRows (rankBoxedRows c P H Q A D)
    let rho := reverseTail c P H Q A D x
    let h := fun t => rho (.inr t) 0
    let q := fun t => blockDefect c (rho (.inr t))
    let u := fun j => rho (.inl j) 0
    readSuccessor (extendedRows c P H Q A D h q u) =
        topRowOperation c (reverseCoeff c x) (buildRows x c G) ∧
      rowSpace (readSuccessor (extendedRows c P H Q A D h q u)) =
        rowSpace (buildRows x c G) ∧
      extensionGamma c H Q D h q u ≠ 0 ∧
      restrictRankBoxRows (Fin.succEmb k) (extendedRows c P H Q A D h q u) =
        rankBoxedRows c P H Q A D := by
  classical
  dsimp only
  let G := flattenRows (rankBoxedRows c P H Q A D)
  let rho := reverseTail c P H Q A D x
  let h := fun t => rho (.inr t) 0
  let q := fun t => blockDefect c (rho (.inr t))
  let u := fun j => rho (.inl j) 0
  let gamma := fun i => -dot x (G i)
  let p := c + ∑ i, reverseCoeff c x i * gamma i
  have hc0 : c ≠ 0 := by intro hz; simp [hz] at hc
  have hpdata := rankBoxedRows_forward_selfDual c P H Q A D
    (by simpa [pow_two] using hc) hD hpm hpp
  have hGli : LinearIndependent K G := flattenRows_linearIndependent _ hpdata.2.1
  have hG : paperSelfDualCode (rowSpace G) := flattenRows_selfDual _ hpdata.2.1 hpdata.1
  have hbuild : paperSelfDualCode (rowSpace (buildRows x c G)) := by
    apply scalar_selfDual _ (buildRows_linearIndependent_of_linearIndependent hc hGli)
      (buildRows_pairwiseOrthogonal hx hc ?_) (by omega)
    intro i j
    exact (flatten_dot _ _).trans (hpdata.1 _ _)
  have heq : topRowOperation c (reverseCoeff c x) (buildRows x c G) =
      borderedRows c p (flattenRow (extensionTail c h q u)) gamma G := by
    rw [kim_lee_top_to_border c _ _ _ hc]
    change borderedRows c p _ gamma G = _
    rw [flatten_reverseTail, reverseTail_shape]
  have hspace := rowSpace_topRowOperation c hc0 (reverseCoeff c x) (buildRows x c G)
  have hB : paperSelfDualCode
      (rowSpace (borderedRows c p (flattenRow (extensionTail c h q u)) gamma G)) := by
    rw [← heq, hspace]
    exact hbuild
  obtain ⟨hp, hg⟩ := extension_parameters_forced c p P H Q A D h q u gamma hc h2 hB
  have hext : readSuccessor (extendedRows c P H Q A D h q u) =
      topRowOperation c (reverseCoeff c x) (buildRows x c G) := by
    rw [extension_dictionary_exact, heq, hp, hg]
  refine ⟨hext, hext ▸ hspace, ?_, ?_⟩
  · intro hz
    apply kim_lee_gamma_ne_zero x G hx hG
    change gamma = 0
    rw [hg, hz]
    rfl
  · exact (paper_rankBoxed_buildingUp_exact c P H Q A D hc h2 hD hpm hpp h q u).2.2.1

end BuildingUpFormalization.Components.RepeatedBox
