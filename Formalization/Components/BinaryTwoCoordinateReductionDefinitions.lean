import Formalization.Components.BinaryRankOneNormalizationDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.BinaryRankOneNormalization

/-- Retain words whose first two coordinates sum to zero. Over F₂ this means
equal coordinates, not the zero-coordinate condition of ordinary shortening. -/
abbrev binaryTwoCoordinateDomain {n : ℕ}
    (C : Submodule (ZMod 2) (Fin (2 + n) → ZMod 2)) :=
  binaryShorteningDomain C

/-- Delete the first two coordinates on the equal-coordinate subcode. -/
abbrev binaryTwoCoordinateMap {n : ℕ}
    (C : Submodule (ZMod 2) (Fin (2 + n) → ZMod 2)) :=
  binaryShorteningMap C

/-- The image of the equal-coordinate subcode under two-coordinate deletion.
The old implementation names are retained solely for compatibility. -/
abbrev binaryReducedCode {n : ℕ}
    (C : Submodule (ZMod 2) (Fin (2 + n) → ZMod 2)) :=
  binaryShortenedCode C

end BuildingUpFormalization.Components.BinaryRankOneNormalization

