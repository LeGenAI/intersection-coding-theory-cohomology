import Formalization.Components.RankBoxedExtensionDefinitions
import Formalization.Components.RankBoxedConstruction

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RankBoxedExtension

open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.RankBoxedStructure

variable {K : Type*} [Field K]

/-- Every valid rank-`r` box admits a new pivot for arbitrary choices of
`h`, `q`, and `u`. Deleting exactly that pivot row and block column recovers
the original matrix, not merely an equivalent code. The same conclusion
can therefore be applied again without any additional hypotheses. -/
theorem paper_rankBoxed_buildingUp_exact {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D) (hpp : PivotGramRelations c P H Q)
    (h q : Fin r → K) (u : Fin k → K) :
    PivotMasterRelations (Fin.cons q Q) (extendA A D q) D ∧
    PivotGramRelations c (extendP c P H Q h q u) (Fin.cons h H) (Fin.cons q Q) ∧
    restrictRankBoxRows (Fin.succEmb k) (extendedRows c P H Q A D h q u) =
      rankBoxedRows c P H Q A D ∧
    RankBoxedPairwiseOrthogonal (extendedRows c P H Q A D h q u) ∧
    LinearIndependent K (extendedRows c P H Q A D h q u) ∧
    rankBoxedRowSpace (extendedRows c P H Q A D h q u) =
      (rankBoxRowBilin (K := K) (k := k + 1) (r := r)).orthogonal
        (rankBoxedRowSpace (extendedRows c P H Q A D h q u)) := by
  classical
  have hpm' : PivotMasterRelations (Fin.cons q Q) (extendA A D q) D := by
    intro s i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [extendA]
    · simpa [extendA] using hpm s i
  have hcross (i : Fin k) :
      c * (u i + (c * (∑ t, q t * Q i t) -
        (∑ t, (h t * Q i t + q t * H i t)) - u i)) +
        ∑ t, (c * (h t * Q i t + q t * H i t) + q t * Q i t) = 0 := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    linear_combination (∑ t, q t * Q i t) * hc
  have hdiag :
      1 + c * ((c / 2 * (1 + ∑ t, q t * q t) - ∑ t, h t * q t) +
        (c / 2 * (1 + ∑ t, q t * q t) - ∑ t, h t * q t)) +
        ∑ t, (c * (h t * q t + q t * h t) + q t * q t) = 0 := by
    have hs : (∑ t, (c * (h t * q t + q t * h t) + q t * q t)) =
        2 * c * (∑ t, h t * q t) + ∑ t, q t * q t := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [hs]
    have hh : c / 2 * 2 = c := div_mul_cancel₀ c h2
    calc
      _ = (c * (c / 2 * 2)) * (1 + ∑ t, q t * q t) +
        (1 + ∑ t, q t * q t) := by ring
      _ = 0 := by rw [hh, ← pow_two, hc]; ring
  have hpp' : PivotGramRelations c (extendP c P H Q h q u)
      (Fin.cons h H) (Fin.cons q Q) := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa [extendP] using hdiag
      · simpa [extendP, eq_comm] using hcross j
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa [extendP, add_comm, mul_comm] using hcross i
      · simpa [extendP] using hpp i j
  refine ⟨hpm', hpp', ?_, ?_⟩
  · funext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp [restrictRankBoxRows, keepRankBoxIndex, extendedRows, rankBoxedRows,
          extendP]
      | inr j => rfl
    | inr i => cases j <;> rfl
  · exact rankBoxedRows_forward_selfDual c _ _ _ _ D
      (by simpa [pow_two] using hc) hD hpm' hpp'

end BuildingUpFormalization.Components.RankBoxedExtension
