import Formalization.Components.QaryRankOneUniversalPairing

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryRankOneOrientedPairing

open BuildingUpFormalization.Components.QaryRankOneUniversalPairing
open BuildingUpFormalization.Components.QaryRankBoxedNormalization

variable {K : Type*} [Field K]

theorem every_qary_selfDualCode_has_rankOne_orientedPairing
    {n : ℕ} (hn : 0 < n) (c : K) (hc : c ^ 2 = (-1 : K))
    (h2 : (2 : K) ≠ 0)
    {C : Submodule K (QaryBlockRow K (Fin n))}
    (hC : QaryBlockSelfDualCode C) :
    HasQaryRankOneOrientedPairing c C :=
  every_qary_selfDualCode_has_rankOne_orientedPairing_exact
    hn c hc h2 hC

end BuildingUpFormalization.Components.QaryRankOneOrientedPairing
