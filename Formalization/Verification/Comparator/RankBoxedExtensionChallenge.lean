import Formalization.Components.RankBoxedExtensionDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RankBoxedExtension

open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.RankBoxedStructure
open BuildingUpFormalization.Components.SplitBoxed

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

theorem paper_rankBoxed_buildingUp_minimal_exact {k r : ℕ} (c : K)
    (b : Fin k → Fin k → K)
    (ell : Fin k → Fin r → SplitBlock K)
    (D : Fin r → Fin r → K)
    (ell0 : Fin r → SplitBlock K) (u : Fin k → K)
    (hc : c * c = -1) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hoff : PaperOffDiagonalRelations c b ell) :
    let b' := extendPaperB c b ell ell0 u
    let ell' := extendPaperEll ell ell0
    PaperOffDiagonalRelations c b' ell' ∧
      restrictRankBoxRows (Fin.succEmb k) (paperRankBoxedRows c b' ell' D) =
        paperRankBoxedRows c b ell D ∧
      RankBoxedPairwiseOrthogonal (paperRankBoxedRows c b' ell' D) ∧
      LinearIndependent K (paperRankBoxedRows c b' ell' D) ∧
      rankBoxedRowSpace (paperRankBoxedRows c b' ell' D) =
        (rankBoxRowBilin (K := K) (k := k + 1) (r := r)).orthogonal
          (rankBoxedRowSpace (paperRankBoxedRows c b' ell' D)) := by
  sorry

end BuildingUpFormalization.Components.RankBoxedExtension
