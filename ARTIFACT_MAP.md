# Manuscript-to-formalization map

The stable labels in `paper.tex` and Lean declaration names identify the results.
Definition, Lemma, Remark and Example have independent section counters.
Theorem, Proposition and Corollary share the theorem counter.

| Current result | Content | Principal exact declaration / suite |
|---|---|---|
| Definitions 2.1--2.2 | Self-duality, Lagrangians, parity | Foundations (22 goals) |
| Proposition 2.1 | Systematic Gram criterion | `paper_systematic_form_criterion_exact` |
| Definition 2.3 | Permutation equivalence | PermutationEquivalence (5) |
| Propositions 2.2--2.3 | Split norm and hyperbolic basis, with 2 nonzero | NormForm (9) |
| Theorems 3.1--3.4 | Cited Kim and Kim--Lee results | BinaryCzKim / QaryForward prove the algebraic forward and adapted-reduction interfaces; the cited converses are not new Lean axioms |
| Theorem 3.5 | Exact self-duality criterion for arbitrary parent matrix | `paper_qary_free_core_boxed_equivalence`; QaryEquivalence (1), QaryForward (21) |
| Theorem 3.6 | Universal rank-r representation, actual code equality | `paperRankBoxedRows_forward_selfDual`, `every_qary_selfDualCode_has_rankBoxed_normalForm`; QaryRankBoxedNormalization (2) |
| Theorem 3.6, restriction and specialization | Same-D restriction, terminal row space, rank-one bridge | RankBoxedStructure (3) |
| Lemma 3.1 | Arbitrary repeatable extension with fixed D | `paper_rankBoxed_buildingUp_minimal_exact`; RankBoxedExtension (2) |
| Lemmas 3.2--3.3 | Fixed-parent Kim--Lee iff, its forced-coefficient specialization, direct sum, converse | RepeatedStep (4), RepeatedBox (7) |
| Example 3.1 | Dense GF(5) code, pairing-dependent ranks one and two, and two extensions with new diagonal blocks $01$ | `Verification/Examples/RankTwoGF5.lean`, four separate kernel certificates; `rank_one_obstruction_audit.cpp` proves that no length-8 or length-10 GF(5) code can be a permutation-invariant rank-two obstruction |
| Theorem 3.7 | Chinburg--Zhang arithmetic realization | Cited published Theorem 1.5; not formalized here |
| Lemma 3.4 | Two-coordinate reduction and exact reconstruction | BinaryTwoCoordinateReduction (3) |
| Theorem 3.8 | Universal binary rank-one representation | `binarySelfDualCode_has_rankOneNormalForm`; BinaryRankOneNormalization (1) |
| Theorem 3.9 | Euclidean realization and exact binary comparison | `paper_binary_cz_kim_corrected`; BinaryCzKim (18) |
| Corollary 3.10 | Explicit normalized rank-one box | SplitBoxed (12), SplitBoxedOrthogonality (12) |
| Theorem 3.11 | Conditional boxed coefficient theorem | `paper_conditional_boxed_normalization_exact`; ConditionalBoxed (1) |
| Explicit change of form in Section 2 | Different named forms, not a Euclidean self-isometry | SplitFormTransport (3) |
| Table 1 | Seven finite-field catalogue entries, five binary Golay levels, both GF(5) repeated levels, both GF(13) repeated levels, public benchmarks, and every exact upward relation | `application_catalog.json`, the three repeated certificates, linked `certificates/*.json`, `build_application_catalog.py`, the public online classifications, and the numerical checkers |
| Proposition 4.1 | Universal rank-one realization of a self-dual MDS $[14,7,8]$ code over $\mathrm{GF}(13)$ | `Examples/LargeGF13.lean` (Gram, normalization, readout, parent, unique correction and reconstruction certificates); `large_applications.json` and `check_large_applications.py` (all $\binom{14}{7}$ minors and exhaustive projective enumeration) |
| GF(5) search baseline | Magma BKLC distances and self-duality status at half dimension for lengths 20, 22, and 24 | `Examples/gf5_bklc_seed_audit.m` and its receipt |

The suite inventory contains **17 suites / 126 distinct declarations**.
Principal declarations are under `BuildingUpFormalization.Components`.
The historical identifiers containing `free_core` are retained to preserve
proof and receipt identities; the manuscript introduces no such terminology.

## Entry points and proof boundaries

`Formalization.Sections.All` imports the section API. Implementations live
in `Formalization/Components/`. Shared definitions still import the frozen
`Formalization/Archive/SubmittedBaseline.lean`; archival placement is not
proof-dependency removal. The 260 baseline theorems are not counted as
260 additional independently compared manuscript goals.

The universal q-ary Challenge fixes a coordinate pairing, requires
`r = finrank (C ⊓ U_c)`, permits a whole-block permutation, and concludes
literal equality with a rank-r generator row space. The binary Challenge
permits scalar-coordinate permutations. Neither substitutes an arbitrary
ambient linear isomorphism for code equivalence.

The arithmetic comparison takes the cohomological image and form isometry as
explicit inputs. Étale cohomology, arithmetic duality and general q-ary
arithmetic realization are outside this artifact's proved claims.

## Numerical data

`applications.json` generates the five smaller examples.
`applications_results.json` records every weight multiplicity, rank and Gram
check.  `build_application_catalog.py` packages these data into stable
per-code certificates and generates the historical comparison in Table 1.
The three repeated-box checkers generate the repeated rows incorporated into
Table 1 and certify the largest binary, GF(5), and GF(13) presentations and
their parent reductions. The separate
large-example pipeline starts from the known
self-dual MDS $[14,7,8]$ code, checks all $\binom{14}{7}=3432$ maximal minors,
normalizes it to the manuscript's rank-one universal form, and exhaustively
checks the unique projective correction class used to reconstruct it from its
$[12,6,6]$ two-coordinate parent.  The Magma replay
`gf13_mds_parent_ad_audit.m` additionally proves that all 182 ordered
two-coordinate reductions of this fixed MDS code have $A_6=960$.

The separate rank-two kernel example has no minimum-distance claim.

## Historical numbering

Submitted Theorem 3.9 corresponds to the corrected criterion, now Theorem 3.5;
submitted Theorem 3.12 corresponds to Corollary 3.10. Older dated receipts
may use intermediate numbering. Resolve them by stable declaration names.
