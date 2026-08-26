import Formalization.Components.BinaryTwoCoordinateReductionDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.BinaryRankOneNormalization

open BuildingUpFormalization.Components.Foundations

theorem mem_binaryReducedCode_iff {n : ℕ}
    (C : Submodule (ZMod 2) (Fin (2 + n) → ZMod 2))
    (w : Fin n → ZMod 2) :
    w ∈ binaryReducedCode C ↔
      ∃ v ∈ C, v 0 = v 1 ∧ splitTail (K := ZMod 2) v = w := by
  sorry

theorem paper_binary_twoCoordinateReduction_exact {n : ℕ}
    {C : Submodule (ZMod 2) (Fin (2 + n) → ZMod 2)}
    {x : Fin (2 + n) → ZMod 2}
    (hC : paperSelfDualCode (K := ZMod 2) C)
    (hxC : x ∈ C) (hx0 : x 0 = 0) (hx1 : x 1 = 1) :
    Function.Injective (binaryTwoCoordinateMap C) ∧
      paperSelfDualCode (K := ZMod 2) (binaryReducedCode C) ∧
      2 * Module.finrank (ZMod 2) (binaryReducedCode C) = n ∧ Even n := by
  sorry

theorem paper_binary_reconstruction_from_reduction_exact {m : ℕ}
    {C : Submodule (ZMod 2) (Fin (2 + 2 * m) → ZMod 2)}
    {x : Fin (2 + 2 * m) → ZMod 2}
    (hC : paperSelfDualCode (K := ZMod 2) C)
    (hxC : x ∈ C) (hx0 : x 0 = 0) (hx1 : x 1 = 1)
    {G : Fin m → Fin (2 * m) → ZMod 2}
    (hG : rowSpace G = binaryReducedCode C) :
    let p := x + allOnes (K := ZMod 2) (2 + 2 * m)
    let z := splitTail (K := ZMod 2) p
    C = rowSpace (buildRowsBin z G) := by
  sorry

end BuildingUpFormalization.Components.BinaryRankOneNormalization

