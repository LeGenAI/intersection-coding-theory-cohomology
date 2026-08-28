import Formalization.Components.QaryRankOneOrientedPairingDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryRankOneOrientedPairing

open BuildingUpFormalization.Components.QaryRankBoxedNormalization

variable {K : Type*} [Field K]

/-- Open exact universal goal: every nonzero-length Euclidean self-dual code
over a split odd-characteristic field admits an oriented coordinate pairing
whose isotropic-line intersection has dimension exactly one. -/
theorem every_qary_selfDualCode_has_rankOne_orientedPairing
    {n : ℕ} (hn : 0 < n) (c : K) (hc : c ^ 2 = (-1 : K))
    (h2 : (2 : K) ≠ 0)
    {C : Submodule K (QaryBlockRow K (Fin n))}
    (hC : QaryBlockSelfDualCode C) :
    HasQaryRankOneOrientedPairing c C := by
  sorry

end BuildingUpFormalization.Components.QaryRankOneOrientedPairing
