import Formalization.Components.BinaryTwoCoordinateReductionDefinitions
import Formalization.Components.BinaryRankOneNormalization

set_option autoImplicit false

namespace BuildingUpFormalization.Components.BinaryRankOneNormalization

open BuildingUpFormalization.Components.Foundations

theorem mem_binaryReducedCode_iff {n : ℕ}
    (C : Submodule (ZMod 2) (Fin (2 + n) → ZMod 2))
    (w : Fin n → ZMod 2) :
    w ∈ binaryReducedCode C ↔
      ∃ v ∈ C, v 0 = v 1 ∧ splitTail (K := ZMod 2) v = w := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, v.1.2, ?_, hv⟩
    exact (eq_neg_of_add_eq_zero_left v.property).trans (CharTwo.neg_eq _)
  · rintro ⟨v, hvC, heq, htail⟩
    have hsum : v 0 + v 1 = 0 := by rw [heq]; exact CharTwo.add_self_eq_zero _
    exact ⟨⟨⟨v, hvC⟩, hsum⟩, htail⟩

/-- Exact statement of the manuscript's binary two-coordinate reduction lemma.
The oriented 01 pivot is indispensable and is an explicit hypothesis. -/
theorem paper_binary_twoCoordinateReduction_exact {n : ℕ}
    {C : Submodule (ZMod 2) (Fin (2 + n) → ZMod 2)}
    {x : Fin (2 + n) → ZMod 2}
    (hC : paperSelfDualCode (K := ZMod 2) C)
    (hxC : x ∈ C) (hx0 : x 0 = 0) (hx1 : x 1 = 1) :
    Function.Injective (binaryTwoCoordinateMap C) ∧
      paperSelfDualCode (K := ZMod 2) (binaryReducedCode C) ∧
      2 * Module.finrank (ZMod 2) (binaryReducedCode C) = n ∧ Even n := by
  have hD := binaryShortenedCode_paperSelfDualCode hC hxC hx0 hx1
  refine ⟨binaryShorteningMap_injective hC hxC hx0 hx1, hD, ?_,
    paperSelfDualCode_even_length hD⟩
  simpa using (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half.mp hD).2

/-- Exact recovery from the reduced code; no ambient isometry replaces equality. -/
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
  exact orientedPivot_reconstructs_from_shortening hC hxC hx0 hx1 hG

end BuildingUpFormalization.Components.BinaryRankOneNormalization

