# Manuscript-to-formalization map

Stable LaTeX labels and Lean declaration names identify the results even if
editorial numbering changes.

| Revision result | Principal formalization |
|---|---|
| Definitions 2.1--2.2 and Proposition 2.1 | `Foundations` (22 goals) |
| Definition 2.3, permutation equivalence | `PermutationEquivalence` (5) |
| Propositions 2.2--2.3, split norm and the two named plane forms | `NormForm` (9), `SplitFormTransport` (3) |
| Theorems 3.1--3.3 | Cited Kim and Chinburg--Zhang theorems; their arithmetic existence statements are inputs, not new Lean axioms |
| Theorem 3.4, Euclidean realization and binary boxed reduction | `BinaryCzKim` (18) |
| Theorems 3.6 and 3.8 | Cited Kim--Lee forward and reverse theorems |
| Theorem 3.9, adapted split reduction and extension | `QaryForward` (21), `QaryEquivalence` (1) |
| Theorem 3.12, split boxed form | `SplitBoxed` (12), `SplitBoxedOrthogonality` (12) |
| Theorem 3.13, conditional boxed normalization | `ConditionalBoxed` (1) |
| Theorem 3.15, universal rank-one normal form after scalar-coordinate permutation | `QaryRankOnePairingMerge` (51), `QaryRankOneUniversalPairing` (1) |
| Supporting rank-boxed existence, restriction, extension, and repeated-step identities | `QaryRankBoxedNormalization` (2), `RankBoxedStructure` (4), `RankBoxedExtension` (2), `RepeatedStep` (4), `RepeatedBox` (9) |
| Binary two-coordinate reduction and universal normalization interfaces | `BinaryTwoCoordinateReduction` (3), `BinaryRankOneNormalization` (1) |
| Propositions 4.1--4.2 | `applications.json`, `check_applications.py`, and generated result data |
| Proposition 4.3 | `check_gf13_repeated_lineage.py`, its source/receipt/results, and `certificates/gf13-repeated-lineage.json` |

The inventory is exactly **19 suites / 181 distinct declarations**. Every
suite has one statement-side Challenge, one completed Solution, one JSON
configuration, and a transitive axiom audit. The only retained application
files are those required by the focused Section 4.
