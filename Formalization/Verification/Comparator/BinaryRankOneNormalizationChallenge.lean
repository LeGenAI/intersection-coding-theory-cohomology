import Formalization.Components.BinaryRankOneNormalizationDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.BinaryRankOneNormalization

open BuildingUpFormalization.Components.Foundations

/-- Exact M6 reverse goal.  The proof must construct a scalar-coordinate
permutation and a literal rank-one Chinburg--Zhang box for every binary
self-dual code; no ambient linear isometry is accepted in place of the
permutation. -/
theorem every_binary_selfDualCode_has_rankOne_normalForm
    {k : ℕ}
    {C : Submodule (ZMod 2) (Fin (2 * (k + 1)) → ZMod 2)}
    (hC : paperSelfDualCode (K := ZMod 2) C) :
    HasBinaryCzRankOneNormalForm C := by
  sorry

end BuildingUpFormalization.Components.BinaryRankOneNormalization
