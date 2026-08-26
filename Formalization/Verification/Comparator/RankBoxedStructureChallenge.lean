import Formalization.Components.RankBoxedStructureDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RankBoxedStructure

open BuildingUpFormalization.Components.SplitBoxed
open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.QaryRankBoxedNormalization

variable {K : Type*} [Field K]

/-- Exact repeated-subbox statement, including the literal restricted rows,
the same core, both restricted Gram laws, and self-duality. -/
theorem paper_rankBoxed_pivot_restriction_exact {l k r : ℕ}
    (s : Fin l ↪ Fin k) (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D) (hpp : PivotGramRelations c P H Q) :
    let R := restrictRankBoxRows s (rankBoxedRows c P H Q A D)
    R = rankBoxedRows c (fun i j => P (s i) (s j))
      (fun i t => H (s i) t) (fun i t => Q (s i) t)
      (fun t j => A t (s j)) D ∧
    PivotMasterRelations (fun i t => Q (s i) t) (fun t j => A t (s j)) D ∧
    PivotGramRelations c (fun i j => P (s i) (s j))
      (fun i t => H (s i) t) (fun i t => Q (s i) t) ∧
    RankBoxedPairwiseOrthogonal R ∧ LinearIndependent K R ∧
    rankBoxedRowSpace R =
      (rankBoxRowBilin (K := K) (k := l) (r := r)).orthogonal
        (rankBoxedRowSpace R) := by
  sorry

/-- Exact terminal code after all pivot rows have been removed. -/
theorem paper_rankBoxed_terminal_exact {r : ℕ} (c : K)
    (P : Fin 0 → Fin 0 → K) (H Q : Fin 0 → Fin r → K)
    (A : Fin r → Fin 0 → K) (D : Fin r → Fin r → K)
    (hD : RankBoxCoreFullRank D) :
    rankBoxedRowSpace (rankBoxedRows c P H Q A D) =
      qaryIsotropicLineCode (K := K) c := by
  sorry

/-- Literal matrix equality and iff of the full hypothesis sets in the
transition from Theorem 3.12 to Theorem 3.13. -/
theorem paper_rankOne_split_specialization_exact {k : ℕ}
    (c : K) (ell : Fin k → SplitBlock K)
    (a : Fin k → K) (b : Fin k → Fin k → K)
    (hc : c ^ 2 = (-1 : K)) :
    rankBoxedRows c (specializationP b) (specializationH ell)
      (specializationQ c ell) (specializationA a) (unitCore (K := K)) =
      (fun i j => splitBoxedRows c ell a b
        (rankOneOptionEquiv k i) (rankOneOptionEquiv k j)) ∧
    ((RankBoxCoreFullRank (unitCore (K := K)) ∧
      PivotMasterRelations (specializationQ c ell) (specializationA a) unitCore ∧
      PivotGramRelations c (specializationP b) (specializationH ell)
        (specializationQ c ell)) ↔
      ((∀ i, dot (ell i) (ell i) = (-1 : K)) ∧
       (∀ i, ell i 0 + c * ell i 1 = -c * a i) ∧
       (∀ i j, i < j → c * (b i j + b j i) + dot (ell i) (ell j) = 0))) := by
  sorry

end BuildingUpFormalization.Components.RankBoxedStructure
