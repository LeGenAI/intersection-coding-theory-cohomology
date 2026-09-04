import Formalization.Components.QaryRankBoxedNormalizationDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RankBoxed

open BuildingUpFormalization.Components.SplitBoxed

variable {K : Type*} [Field K]

/-- Exact forward goal for the minimal paper form `G(c;Q,ell,D)`. -/
theorem paperRankBoxedRows_forward_selfDual {k r : ℕ} (c : K)
    (Q : Fin k → Fin k → K)
    (ell : Fin k → Fin r → SplitBlock K)
    (D : Fin r → Fin r → K)
    (hc : c * c = -1) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hoff : PaperOffDiagonalRelations c Q ell) :
    RankBoxedPairwiseOrthogonal (paperRankBoxedRows c Q ell D) ∧
      LinearIndependent K (paperRankBoxedRows c Q ell D) ∧
      rankBoxedRowSpace (paperRankBoxedRows c Q ell D) =
        (rankBoxRowBilin (K := K) (k := k) (r := r)).orthogonal
          (rankBoxedRowSpace (paperRankBoxedRows c Q ell D)) := by
  sorry

end BuildingUpFormalization.Components.RankBoxed

namespace BuildingUpFormalization.Components.QaryRankBoxedNormalization

variable {K : Type*} [Field K]

/-- Every Euclidean self-dual code over a split field admits the literal
rank-`r` boxed normal form after a block-coordinate permutation. -/
theorem every_qary_selfDualCode_has_rankBoxed_normalForm
    {n : ℕ} (c : K) (hc : c ^ 2 = (-1 : K))
    (h2 : (2 : K) ≠ 0)
    {C : Submodule K (QaryBlockRow K (Fin n))}
    (hC : QaryBlockSelfDualCode C) :
    HasQaryRankBoxedNormalForm c C := by
  sorry

end BuildingUpFormalization.Components.QaryRankBoxedNormalization
