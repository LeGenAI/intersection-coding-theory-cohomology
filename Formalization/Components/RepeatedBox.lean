import Formalization.Components.RepeatedBoxDefinitions
import Formalization.Components.RepeatedStep
import Formalization.Components.RankBoxedExtension

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RepeatedBox

open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.RankBoxedStructure
open BuildingUpFormalization.Components.RankBoxedExtension
open BuildingUpFormalization.Components.RepeatedStep
open BuildingUpFormalization.Components.Foundations

variable {K : Type*} [Field K]

omit [Field K] in
@[simp] theorem unflatten_flatten {k r : ℕ} (R : RankBoxRow K k r) :
    unflattenRow (flattenRow R) = R := by
  funext j t
  simp only [unflattenRow, flattenRow, Equiv.symm_apply_apply]

omit [Field K] in
@[simp] theorem flatten_unflatten {k r : ℕ} (v : Fin ((k + r) * 2) → K) :
    flattenRow (unflattenRow (k := k) (r := r) v) = v := by
  funext j
  simp only [unflattenRow, flattenRow, Equiv.apply_symm_apply,
    Prod.mk.eta]

theorem flatten_dot {k r : ℕ} (R S : RankBoxRow K k r) :
    dot (flattenRow R) (flattenRow S) = rankBoxRowInner R S := by
  unfold dot flattenRow rankBoxRowInner
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp only [Equiv.symm_apply_apply]
  rfl

theorem extension_dictionary_exact {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (h q : Fin r → K) (u : Fin k → K) :
    readSuccessor (extendedRows c P H Q A D h q u) =
      borderedRows c (c / 2 * (1 + ∑ t, q t * q t) - ∑ t, h t * q t)
        (flattenRow (extensionTail c h q u))
        (fun i => extensionGamma c H Q D h q u (finSumFinEquiv.symm i))
        (flattenRows (rankBoxedRows c P H Q A D)) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.addCases ?_ ?_ j
    · intro t
      fin_cases t <;> rfl
    · intro j
      simp only [readSuccessor, borderedRows, Fin.cons_zero, prepend2, Fin.append_right]
      unfold flattenRow
      cases finSumFinEquiv.symm (finProdFinEquiv.symm j).1 <;>
        simp [extendedRows, rankBoxedRows, keepRankBoxIndex, extendP,
          extensionTail, splitAffineBlock, eq_comm]
  · refine Fin.addCases ?_ ?_ j
    · intro t
      cases hi : finSumFinEquiv.symm i <;> fin_cases t <;>
        simp [readSuccessor, borderedRows, extendedRows, rankBoxedRows,
          keepRankBoxIndex, extendP, extendA, extensionGamma, prepend2,
          splitAffineBlock, SplitBoxed.isotropicLineBlock, head2, hi]
    · intro j
      simp only [readSuccessor, borderedRows, Fin.cons_succ, prepend2, Fin.append_right]
      unfold flattenRows flattenRow
      cases finSumFinEquiv.symm i <;>
        cases finSumFinEquiv.symm (finProdFinEquiv.symm j).1 <;>
        simp [extendedRows, rankBoxedRows, keepRankBoxIndex, extendP, extendA]

theorem extension_zero_column_iff {k r : ℕ} (c : K)
    (H Q : Fin k → Fin r → K) (D : Fin r → Fin r → K)
    (hD : RankBoxCoreFullRank D) (h q : Fin r → K) (u : Fin k → K) :
    extensionGamma c H Q D h q u = 0 ↔
      q = 0 ∧ ∀ i, u i = -(∑ t, Q i t * h t) := by
  classical
  constructor
  · intro hg
    have hDq : Matrix.mulVec D q = Matrix.mulVec D 0 := by
      funext s
      have hs := congrFun hg (.inr s)
      simpa [extensionGamma, Matrix.mulVec, dotProduct, mul_comm] using neg_eq_zero.mp hs
    have hq : q = 0 :=
      Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det D).mpr
        (isUnit_iff_ne_zero.mpr hD)) hDq
    refine ⟨hq, ?_⟩
    intro i
    have hi := congrFun hg (.inl i)
    simp [extensionGamma, hq] at hi
    simpa [mul_comm] using (sub_eq_zero.mp hi).symm
  · rintro ⟨rfl, hu⟩
    funext i
    cases i <;> simp [extensionGamma, hu, mul_comm]

private def flattenLinearMap {k r : ℕ} :
    RankBoxRow K k r →ₗ[K] (Fin ((k + r) * 2) → K) where
  toFun := flattenRow
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flattenRows_linearIndependent {k r : ℕ}
    (R : RankBoxIndex k r → RankBoxRow K k r) (hR : LinearIndependent K R) :
    LinearIndependent K (flattenRows R) := by
  have hinj : Function.Injective (flattenLinearMap (K := K) (k := k) (r := r)) := by
    intro x y h
    have := congrArg unflattenRow h
    simpa [flattenLinearMap] using this
  exact (hR.map' flattenLinearMap (LinearMap.ker_eq_bot.mpr hinj)).comp
    finSumFinEquiv.symm finSumFinEquiv.symm.injective

theorem scalar_selfDual {m n : ℕ} (G : Matrix (Fin m) (Fin n) K)
    (hli : LinearIndependent K G) (ho : PairwiseOrthogonal G) (hn : 2 * m = n) :
    paperSelfDualCode (rowSpace G) := by
  apply paperSelfDualCode_iff_totallyIsotropic_and_finrank_half.mpr
  refine ⟨rowSpace_le_orthogonal_of_pairwiseOrthogonal ho, ?_⟩
  rw [show Module.finrank K (rowSpace G) = m by
    simpa [rowSpace] using finrank_span_eq_card hli]
  simpa using hn

theorem flattenRows_selfDual {k r : ℕ}
    (R : RankBoxIndex k r → RankBoxRow K k r) (hli : LinearIndependent K R)
    (ho : RankBoxedPairwiseOrthogonal R) :
    paperSelfDualCode (rowSpace (flattenRows R)) := by
  apply scalar_selfDual _ (flattenRows_linearIndependent R hli) ?_ (by omega)
  intro i j
  exact (flatten_dot _ _).trans (ho _ _)

theorem bordered_linearIndependent {m n : ℕ} (c p : K) (rho : Fin n → K)
    (gamma : Fin m → K) (G : Matrix (Fin m) (Fin n) K)
    (hG : LinearIndependent K G) :
    LinearIndependent K (borderedRows c p rho gamma G) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have h0 := congrFun ha (Fin.castAdd n (0 : Fin 2))
  have h1 := congrFun ha (Fin.castAdd n (1 : Fin 2))
  simp [Fin.sum_univ_succ, borderedRows, prepend2, head2] at h0 h1
  have hs : (∑ j, a j.succ * (c * gamma j)) = c * ∑ j, a j.succ * gamma j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs] at h1
  have ha0 : a 0 = 0 := by linear_combination h1 - c * h0
  have htail : ∑ j, a j.succ • G j = 0 := by
    funext j
    have hj := congrFun ha (Fin.natAdd 2 j)
    simpa [Fin.sum_univ_succ, borderedRows, prepend2, ha0] using hj
  exact Fin.cases ha0 (fun j => Fintype.linearIndependent_iff.mp hG _ htail j) i

theorem readRow_dot {k r : ℕ} (R S : RankBoxRow K (k + 1) r) :
    dot (prepend2 (R (.inl 0) 0) (R (.inl 0) 1)
        (flattenRow (fun j => R (keepRankBoxIndex (Fin.succEmb k) j))))
      (prepend2 (S (.inl 0) 0) (S (.inl 0) 1)
        (flattenRow (fun j => S (keepRankBoxIndex (Fin.succEmb k) j)))) =
      rankBoxRowInner R S := by
  rw [dot_prepend2_prepend2, flatten_dot]
  simp only [rankBoxRowInner, Fin.sum_univ_succ, keepRankBoxIndex,
    Sum.map_inl, Sum.map_inr, Fin.coe_succEmb, id_eq]
  simp only [SplitBoxed.splitBlockInner, dot, Fin.sum_univ_two]
  ring

theorem readSuccessor_pairwise {k r : ℕ}
    (R : RankBoxIndex (k + 1) r → RankBoxRow K (k + 1) r)
    (ho : RankBoxedPairwiseOrthogonal R) : PairwiseOrthogonal (readSuccessor R) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    exact (readRow_dot _ _).trans (ho _ _)

theorem repeated_step_selfDual_exact {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D) (hpp : PivotGramRelations c P H Q)
    (h q : Fin r → K) (u : Fin k → K) :
    paperSelfDualCode (rowSpace (flattenRows (rankBoxedRows c P H Q A D))) ∧
    paperSelfDualCode (rowSpace (readSuccessor (extendedRows c P H Q A D h q u))) := by
  have hparent := rankBoxedRows_forward_selfDual c P H Q A D
    (by simpa [pow_two] using hc) hD hpm hpp
  have hchild := paper_rankBoxed_buildingUp_exact c P H Q A D hc h2 hD hpm hpp h q u
  refine ⟨flattenRows_selfDual _ hparent.2.1 hparent.1, ?_⟩
  apply scalar_selfDual _ ?_ (readSuccessor_pairwise _ hchild.2.2.2.1) (by omega)
  rw [extension_dictionary_exact]
  exact bordered_linearIndependent _ _ _ _ _ (flattenRows_linearIndependent _ hparent.2.1)

theorem repeated_step_normalization_exact {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D) (hpp : PivotGramRelations c P H Q)
    (h q : Fin r → K) (u : Fin k → K) (s : Fin (k + r))
    (hs : extensionGamma c H Q D h q u (finSumFinEquiv.symm s) ≠ 0) :
    let p := c / 2 * (1 + ∑ t, q t * q t) - ∑ t, h t * q t
    let rho := flattenRow (extensionTail c h q u)
    let gamma := fun i => extensionGamma c H Q D h q u (finSumFinEquiv.symm i)
    let G := flattenRows (rankBoxedRows c P H Q A D)
    let x := normalizedTail c p rho gamma G s
    dot x x = -1 ∧ (∀ i, dot x (G i) = -gamma i) ∧
      topRowOperation c⁻¹ (Pi.single s (c⁻¹ * normalizingCoeff c p gamma s))
        (readSuccessor (extendedRows c P H Q A D h q u)) = buildRows x c G ∧
      rowSpace (readSuccessor (extendedRows c P H Q A D h q u)) =
        rowSpace (buildRows x c G) ∧
      (∀ i j, buildRows x c G i.succ (Fin.natAdd 2 j) = G i j) := by
  obtain ⟨hG, hB⟩ := repeated_step_selfDual_exact c P H Q A D hc h2 hD hpm hpp h q u
  rw [extension_dictionary_exact] at hB
  dsimp only
  simpa only [extension_dictionary_exact, normalizedBorder] using
    one_step_normalization_exact _ _ _ _ _ hc hG hB s hs

theorem repeated_step_kim_lee_iff {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D) (hpp : PivotGramRelations c P H Q)
    (h q : Fin r → K) (u : Fin k → K) :
    (∃ x, dot x x = -1 ∧
      rowSpace (readSuccessor (extendedRows c P H Q A D h q u)) =
        rowSpace (buildRows x c (flattenRows (rankBoxedRows c P H Q A D)))) ↔
      ¬ (q = 0 ∧ ∀ i, u i = -(∑ t, Q i t * h t)) := by
  obtain ⟨hG, hB⟩ := repeated_step_selfDual_exact c P H Q A D hc h2 hD hpm hpp h q u
  rw [extension_dictionary_exact] at hB ⊢
  rw [one_step_kim_lee_iff _ _ _ _ _ hc h2 hG hB,
    ← extension_zero_column_iff c H Q D hD h q u]
  apply not_congr
  constructor
  · intro heq
    funext i
    simpa using congrFun heq (finSumFinEquiv i)
  · intro heq
    rw [heq]
    rfl

/-- Exact fixed-parent criterion after removing the redundant
master-by-pivot coefficient matrix. -/
theorem determined_repeated_step_kim_lee_iff {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D) (hpp : PivotGramRelations c P H Q)
    (h q : Fin r → K) (u : Fin k → K) :
    (∃ x, dot x x = -1 ∧
      rowSpace (readSuccessor
        (extendedRows c P H Q (forcedMasterCoefficients Q D) D h q u)) =
      rowSpace (buildRows x c
        (flattenRows (determinedRankBoxedRows c P H Q D)))) ↔
      ¬ (q = 0 ∧ ∀ i, u i = -(∑ t, Q i t * h t)) := by
  apply repeated_step_kim_lee_iff c P H Q
    (forcedMasterCoefficients Q D) D hc h2 hD
  · intro s i
    simp [forcedMasterCoefficients]
  · exact hpp

end BuildingUpFormalization.Components.RepeatedBox
