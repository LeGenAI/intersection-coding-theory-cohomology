import Formalization.Components.BinaryRankOneNormalizationInduction

/-!
# Universal binary rank-one normalization

This section fixes the reverse M6 target with the same quantifiers as the
natural-language theorem: every binary self-dual code is to be carried by a
scalar-coordinate permutation to a literal Chinburg--Zhang rank-one box.

The trusted implementation proves the coordinate-flattening isometry, the
exact forward certificate, the all-ones invariant, the length-two base case,
the self-dual two-coordinate shortening, the corrected one-step boxed
extension, and the full Chinburg--Zhang induction.  The universal conclusion
is `binarySelfDualCode_has_rankOneNormalForm`; it constructs only scalar
coordinate permutations and proves the displayed diagonal and opposite-block
laws for the resulting literal box.
-/
