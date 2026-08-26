import Formalization.Components.RankBoxedExtensionDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RankBoxedExtension

open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.RankBoxedStructure

variable {K : Type*} [Field K]

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
  sorry

end BuildingUpFormalization.Components.RankBoxedExtension
