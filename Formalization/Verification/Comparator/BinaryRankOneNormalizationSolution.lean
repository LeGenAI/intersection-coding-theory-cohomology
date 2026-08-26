import Formalization.Components.BinaryRankOneNormalizationInduction

set_option autoImplicit false

namespace BuildingUpFormalization.Components.BinaryRankOneNormalization

open BuildingUpFormalization.Components.Foundations

theorem every_binary_selfDualCode_has_rankOne_normalForm
    {k : ℕ}
    {C : Submodule (ZMod 2) (Fin (2 * (k + 1)) → ZMod 2)}
    (hC : paperSelfDualCode (K := ZMod 2) C) :
    HasBinaryCzRankOneNormalForm C :=
  binarySelfDualCode_has_rankOneNormalForm hC

end BuildingUpFormalization.Components.BinaryRankOneNormalization
