import Formalization.Components.RankBoxedConstruction
import Formalization.Components.RankBoxedStructure
import Formalization.Components.RankBoxedExtension
import Formalization.Components.RepeatedBoxConverse

/-!
# Rank-boxed construction and its current proof boundary

This section owns the new rank-`r` boxed generator matrix.  It keeps the
lower-right `r × r` core free, records its independent full-rank condition,
and proves the exact characteristic-two rank-one specialization to the
Chinburg--Zhang block form used in Theorem 3.4.

The reverse theorem asserting that every q-ary self-dual code can be placed
in this form is deliberately not claimed by this module; it is the next
normalization layer.  In particular, the exact binary theorem is recovered
at `r = 1`; a general rank-`r` characteristic-two instance is not identified
with that rank-one normal form without an additional coordinate-pairing
argument.
-/
