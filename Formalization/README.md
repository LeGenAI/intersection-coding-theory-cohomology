# Modular Lean layout

`Components/` contains proof implementations. `Sections/` exposes stable
imports following the mathematical exposition. `Verification/` contains
axiom audits and independent Challenge/Solution pairs.

| Component family | Implementation modules | Exact goals |
|---|---|---:|
| Bilinear foundations and systematic form | `Foundations*` | 22 |
| Permutation equivalence | `PermutationEquivalence*` | 5 |
| Split norm form and exact preliminary propositions | `NormForm*` | 9 |
| Binary building-up | `BinaryCzKim*` | 18 |
| Universal binary rank-one normalization | `BinaryRankOneNormalization*` | 1 |
| Universal q-ary rank-`r` normalization | `QaryRankBoxedNormalization*` | 1 |
| Repeated boxed structure and exact rank-one specialization | `RankBoxedStructure*` | 3 |
| Repeatable rank-boxed building-up with fixed D | `RankBoxedExtension*` | 1 |
| One-step Kim--Lee normalization, exception and binary specialization | `RepeatedStep*` | 4 |
| Fixed-parent repeated-box correspondence in both directions | `RepeatedBox*` | 6 |
| Split q-ary forward and adapted reduction | `QaryForward*` | 21 |
| Q-ary building-up self-duality criterion | `QaryEquivalence*` | 1 |
| Boxed-row independence and ambient form | `SplitBoxed*` | 12 |
| Exact boxed theorem | `SplitBoxedOrthogonality*` | 12 |
| Binary two-coordinate reduction and reconstruction | `BinaryTwoCoordinateReduction*` | 3 |
| Change of bilinear form | `SplitFormTransport*` | 3 |
| Exact conditional coefficient theorem | `ConditionalBoxed*` | 1 |
| **Total** | | **123** |

Every completed family has a separate statement-only Comparator Challenge, completed
Solution, JSON configuration, and transitive axiom-audit module.
All 123 goals in seventeen suites passed a fresh complete Linux Comparator
replay on 2026-08-27, including default-kernel and transitive axiom checks.
This final run supersedes the earlier incremental coverage records.
The dated current verification record is in
[Verification/Comparator/RESULTS.md](Verification/Comparator/RESULTS.md).
The public AFM artifact does not include the separate arithmetic follow-up.

The universal q-ary rank-`r` existence theorem for Theorem 3.6 (formerly 3.12) is implemented
in `Components/QaryRankBoxedNormalization.lean`.  Its exact statement-only
Challenge, completed Solution, JSON configuration, transitive axiom audit,
Linux build, and default-kernel Comparator replay all pass.  It is included in
the current 123-declaration inventory.

## Rank-boxed construction

`RepeatedStep.lean`, `RepeatedBox.lean` and `RepeatedBoxConverse.lean`
prove Lemmas 3.2--3.3 and the binary specialization. Nonzero gamma gives
an explicit top-row operation to literal `buildRows` with all parent tails
unchanged. Gamma zero is exactly a length-two direct-sum addition, and in
the repeated coefficients it is equivalent to q=0 and u-transpose=-Qh-transpose.
Conversely, every norm-minus-one Kim--Lee vector yields the literal same-D
successor by the prescribed top-row operation. No arbitrary coordinate
isometry or self-duality-only substitute is used.
See `Verification/Comparator/RESULTS.md`.

`RankBoxedExtension.lean` proves Lemma 3.1 following
Theorem 3.6. Every valid box admits a new pivot for arbitrary h, q, u over
a field with 2 nonzero and c²=-1. The conclusion includes both new Gram
relations, exact parent recovery, independent orthogonal rows, and
self-duality with unchanged D. It can be reapplied at every step.
Its independent Linux Comparator/default-kernel replay passes. The separate
GF(5) example verifies [8,4] -> [10,5] -> [12,6], including literal
Kim--Lee identities and both reverse restrictions.

`RankBoxedStructure.lean` proves the exact structural continuation of
Theorem 3.6 and its transition to Corollary 3.10. An arbitrary embedding of
retained pivot indices restricts both rows and block columns; the resulting
matrix has the same core, restricted Gram relations, independent orthogonal
rows, and a self-dual row space. The zero-pivot terminal row space is exactly
the isotropic-line code. The rank-one theorem gives literal matrix equality
and an iff of hypothesis sets, explicitly imposing zero pivot diagonal.
These three exact declarations pass the independent Linux Comparator suite
`RankBoxedStructure.json`, default-kernel replay, and transitive axiom audit.

`RankBoxedDefinitions.lean` and `RankBoxedConstruction.lean` add 42 theorem
declarations for the new rank-`r` boxed matrix.  They retain a general
`r × r` terminal matrix `D`, prove the exact Gram relations, and recover the literal
Theorem 3.8 (formerly 3.4) block pattern at `q = 2` and `r = 1`.  A nonzero determinant of
the terminal matrix proves linear independence, and the complete forward theorem
proves that the resulting row space is Euclidean self-dual.  The intrinsic
version assumes linear independence directly; under the mixed-row Gram
relation this is equivalent to `det D ≠ 0`.  The rank-one unit core is proved
full rank over every field, explaining why the normalized binary theorem has
no visible determinant side condition.  These declarations are included in
the transitive axiom audit.  The exact universal binary reverse theorem is
counted separately as one Comparator declaration.

## Exact binary reverse-normalization goal

`BinaryRankOneNormalizationDefinitions.lean` fixes the universal reverse statement
without weakening code equivalence: for every binary self-dual code of length
`2 * (k + 1)`, one scalar-coordinate permutation must carry the code to the
row space of `binaryCzRankOneFinRows b`, with `b i i = 0` and
`b i j + b j i = 1` off the diagonal.  The trusted implementation proves
coordinate flattening, preservation of the Euclidean product and row
independence, the all-ones invariant, existence of a normalized `01` pivot,
the complete forward certificate, the length-two base case, injectivity of
the two-coordinate reduction map, and self-duality of the resulting code. It
also moves an arbitrary selected
`01` pair to the literal head by a scalar-coordinate permutation and proves
that the original code is exactly the Kim row space reconstructed from any
row family spanning the reduced code. Finally, it performs the explicit
one-step row normalization of that Kim family to the larger literal box and
composes all scalar-coordinate permutations.

`binarySelfDualCode_has_rankOneNormalForm` closes the induction.  The
statement-exact `BinaryRankOneNormalizationChallenge.lean`, completed
Solution, JSON configuration, axiom audit, Linux build, and Linux Comparator
replay all pass.  The trusted theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Form transport and two-coordinate reduction

`SplitFormTransport` states both forms explicitly: standard Euclidean on the
source, and Gram block [[0,2],[2,0]] followed by a Euclidean tail on the target.
It expands the archived `SplitIsometryCodeEquiv` predicate and proves that
the alignment map is NOT a Euclidean isometry. This auxiliary transport is
not permutation equivalence and is not the proof of Theorem 3.11.

`ConditionalBoxed` instead proves the full exact Theorem 3.11 directly from
self-duality, a generator row space, and every displayed block condition.
It gives the literal matrix, all three coefficient relations, and the code
row-space equality without changing forms.

`BinaryTwoCoordinateReduction` exposes `binaryTwoCoordinateMap` and
`binaryReducedCode`. These are definitionally equal to the older internal
shortening names, retained for compatibility. The operation retains equal
coordinates (00 or 11), unlike ordinary shortening which retains 00 only.
Its three independent goals cover membership, the full reduction lemma
(injectivity, self-duality, half-dimension, and evenness), and reconstruction.
The oriented 01 pivot is an explicit hypothesis.

Manuscript numbering is resolved by `ARTIFACT_MAP.md`. Historical source
comments and receipts may use earlier numbers; certified Lean/Challenge
source files were not changed by the numbering-only revision.
