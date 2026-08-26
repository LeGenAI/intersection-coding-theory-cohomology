import Formalization.Components.QaryRankBoxedNormalizationDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryRankBoxedNormalization

variable {K : Type*} [Field K]

/-- Every Euclidean self-dual code over a split field admits the literal
rank-`r` boxed normal form after a block-coordinate permutation. -/
theorem every_qary_selfDualCode_has_rankBoxed_normalForm
    {n : ℕ} (c : K) (hc : c ^ 2 = (-1 : K))
    {C : Submodule K (QaryBlockRow K (Fin n))}
    (hC : QaryBlockSelfDualCode C) :
    HasQaryRankBoxedNormalForm c C := by
  sorry

end BuildingUpFormalization.Components.QaryRankBoxedNormalization
