# Exact rank-one pairing goals

The completed cross-pair rank goal is

\[
 \dim_K\left\langle
   (-c,a),(1,b),(0,d_i)_{i\in\iota}
 \right\rangle=|\iota|+1,
\]

under the exact hypotheses that `c` is nonzero, the family `(d_i)` is
linearly independent, and `a+c b` lies in its span.  This is the rank
calculation required when a split length-two summand is cross-paired with a
selected parent coordinate pair.  The statement is implemented as
`paper_qary_rankOne_crossPair_merge_exact`; its Challenge imports definitions
only and contains no part of the proof.

The selected parent column enters naturally as the defect `b-c a`, rather
than directly as `a+c b`.  The accepted companion bridge now proves the full
implication

\[
 \sum_j \lambda_j m_j=0,\quad \lambda_{j_0}\ne0
 \quad\Longrightarrow\quad
 a+c b\in\langle d_i:i\ne j_0\rangle
 \quad\Longrightarrow\quad
 \dim\langle(-c,a),(1,b),(0,d_i)\rangle=|\iota|+1,
\]

where `m_{j_0}=b-c a`; the equality
`a+c b=c(b-c a)` uses `c²=-1`.

This declaration deliberately does **not** claim the universal rank-one
normalization theorem.  Its exact prerequisites are separated into the
following closed goals.

The corank-one selection item is closed by
`exists_selected_defect_relation_of_corank_one_exact`: the hypothesis is only
that the defect-column span has dimension one below the number of columns,
and the conclusion supplies both a nonzero selected coefficient and linear
independence of the complementary columns.

The literal identification and defect-nullity items are also closed:
`crossPairedDirectSumDefects_eq_crossPairDefects` computes the two new columns
from `(1,0)`, `(c,0)`, `(0,a)`, and `(0,b)`, while
`exists_crossPaired_directSum_defect_rank_of_corank_one_exact` composes that
calculation with corank-one selection.  The square rank--nullity bridge
`columnEvaluationDual_kernel_finrank_one_exact` identifies codimension one of
the defect columns with a one-dimensional dual evaluation kernel, and
`exists_crossPaired_directSum_defect_nullity_one_exact` applies it to the
selected direct-sum branch.  Finally,
`blockColumnGenerator_intersection_finrank_one_exact` maps that kernel into
the generated block code and proves that its intersection with `U_c` has
dimension one.  Generator injectivity is stated explicitly; it is the exact
row-independence condition needed to preserve the kernel dimension.

The literal child-column layer is now closed as well.
`crossPairedDirectSumColumns_defect_eq` verifies the two cross-paired columns
and every unchanged parent pair, while
`crossPairedDirectSum_blockColumnGenerator_injective` proves that an injective
parent generator remains injective.  Their composition with the preceding
rank results is
`exists_crossPaired_directSum_code_intersection_finrank_one_exact`, the full
direct-sum branch at the generated-code level.

The arbitrary-code realization is also closed by
`canonicalBlockCodeGenerator_exact`.  The first and second scalar-coordinate
functionals on `C` define a generator on `C**`; the natural bidual evaluation
equivalence proves this generator injective and its range literally equal to
`C`.

The remaining numerical bridge is now closed by
`blockColumnGenerator_defect_rank_add_intersection_finrank_exact`: defect rank
plus intersection dimension equals the coefficient-space dimension.
`canonicalBlockCode_defect_corank_of_intersection_one_exact` specializes this
to turn `dim(C ∩ U_c)=1` into canonical defect corank one.  Finally,
`exists_crossPaired_canonicalCode_directSum_intersection_one_exact` proves
rank-one preservation for the cross-paired split direct sum of an arbitrary
parent block code.

The coordinate claim is no longer implicit.  `crossPairScalarEquiv` is the
explicit permutation of individual scalar coordinates, and
`crossPairedGenerator_eq_scalarCoordinateReindex_exact` proves equality of
the resulting generators.  The code-level equality is
`crossPairedCode_eq_scalarCoordinateReindex_exact`.

The finite-index direct-sum step is closed by
`finCrossPair_scalarCoordinatePermuted_directSum_exact` and
`finCanonicalSplitDirectSum_has_rankOne_orientedPairing_exact`.  The first
conjugates the generic cross-pairing to an explicit permutation of
`Fin (n+1) × Fin 2`; the second proves the exact
`HasQaryRankOneOrientedPairing` conclusion.

The auxiliary graph-form Kim--Lee step is closed at the block-code level.
`qaryBlockDefectLinear_kimLeeBlockGenerator_exact` computes the child defect
as `(-c a, defect(z))`, and
`kimLeeBlockCode_inf_qaryIsotropicLineCode_finrank_exact` proves equality of
the child and parent intersection dimensions.  Its finite-index consequence is
`finKimLeeBlockCode_has_rankOne_orientedPairing_exact`.  This auxiliary
generator copies the old tail `z` and is not by itself the scalar
`buildRows` matrix.

The literal building-up branch is now closed separately and exactly.
`buildingUpBlockGenerator` contains the necessary old tail `a x + z`.
`qaryBlockDefectLinear_buildingUpBlockGenerator_exact` computes its new
defect as `-c a`; `buildingUpBlockCode_inf_qaryIsotropicLineCode_finrank_exact`
therefore proves exact preservation of the intersection dimension.  Finally,
`prependedScalarRowSpace_buildRows_eq_buildingUpBlockCode_exact` identifies
this block code with `rowSpace (buildRows x c G)` as a literal submodule
equality after consecutive scalar coordinates are grouped into blocks.

The matrix-level recursion is now closed.  The theorem
`paper_rankBoxed_successor_dictionary_exact` identifies every nonterminal
rank box literally with one `extendedRows` successor of its first-pivot
restriction.  The theorem `paper_rankBoxed_head_step_kim_lee_iff` then gives
the exhaustive first-pivot dichotomy: the successor is a Kim--Lee step exactly
when its correction coefficient is nonzero; its complement is the exact
zero-correction direct-sum branch.  The zero-pivot terminal row space was
already identified with the isotropic-line code.

The scalar direct-sum interface is now closed as well.
`prependedScalarRowSpace_directSumRows_exact` identifies the exceptional
matrix branch with `K(1,-c) \oplus C`.  The exact new-coordinate swap is
`headSwap_directSumBlockCode_neg_exact`; its finite conjugate is
`finLastSwap_directSumBlockCode_neg_exact`.  Together with the literal
canonical/direct-sum equality, these yield
`finDirectSumBlockCode_neg_has_rankOne_orientedPairing_exact`.

The accumulated parent permutation is now transported exactly through both
children.  For the literal direct-sum child this is
`finExtendOld_directSumBlockCode_exact`; hence
`finDirectSumBlockCode_neg_has_rankOne_orientedPairing_of_parent_exact`
requires only `HasQaryRankOneOrientedPairing` for the parent.  For the
nonzero literal building-up child,
`finExtendOld_buildingUpBlockCode_exact` transports the parent code, the
correction word, and the dual functional, and
`finBuildingUpBlockCode_has_rankOne_orientedPairing_of_parent_exact` gives the
same permutation-free induction step.  The remaining universal work is the
exact iteration of these two child theorems along the rank-box successor
dictionary from the terminal isotropic-line code.

The successor interface is also exhaustive at the literal row-space level:
`repeated_step_rowSpace_dichotomy_exact` returns either an exact `buildRows`
equality or an exact `directSumRows` equality, so the final iteration no
longer has to reconstruct the zero branch from an iff.

The ultimate statement is frozen in
`QaryRankOneUniversalPairingChallenge.lean` and is now matched by an independent
Solution and JSON acceptance configuration. Its permutation acts
on `Fin n × Fin 2`, so it permits arbitrary re-pairing and reversal of scalar
coordinates rather than merely permuting already chosen two-coordinate
blocks.  The assumptions explicitly include `0 < n`, `c² = -1`, and `2 ≠ 0`;
the conclusion is exactly that the permuted code intersects `U_c` in dimension
one. It is declaration 181 in the accepted inventory.
