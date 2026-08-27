# Reproducible examples

The small application matrices catalogued by the manuscript are checked with:

```sh
python3 Formalization/Verification/Examples/check_applications.py --check
python3 Formalization/Verification/Examples/check_golay_lineage.py --check
python3 Formalization/Verification/Examples/check_gf5_repeated_top.py --check
python3 Formalization/Verification/Examples/check_gf13_repeated_lineage.py --check
python3 Formalization/Verification/Examples/build_application_catalog.py --check
```

The first large-application baseline starts from the known pure
double-circulant self-dual MDS `[14,7,8]` code over `GF(13)` and runs:

```sh
python3 Formalization/Verification/Examples/check_large_applications.py --check
lake env lean Formalization/Verification/Examples/LargeGF13.lean
```

The catalogue builder creates stable linked certificates for every Table 1
row.  It records the exact parent identifier separately from the historical
distance and weight-enumerator benchmark; a benchmark $A_d$ is not treated as
an extremal quantity when several optimal weight enumerators exist.

In Table 1, bold $A_d$ values match the smallest coefficient in the public
comparisons cited there.  For the binary rows they agree with the minimum at
the best distance in the complete
[online binary classification](https://www.math.is.tohoku.ac.jp/~mharada/research/codes/sd2.htm),
and the two short quinary rows agree with the corresponding minima in the
complete [GF(5) classification](https://www.math.is.tohoku.ac.jp/~mharada/research/codes/sd5.htm).
The GF(13) MDS values are fixed by the MDS weight enumerator.  At unclassified
lengths, bold means equality with the smallest public coefficient located in
the cited comparison, not a global minimum claim.  In particular, exact Magma enumeration of
the public Kim--Choi generator of a self-dual `[18,9,8]` code over `GF(13)`
gives $A_8=1752$, below both our value 1896 and the earlier published value
2484.  The GF(13) replay verifies this comparison together with our code.

The binary Golay checker supplies the binary rows of Table 1. It reduces the
standard extended Golay generator four times and verifies the exact inverse Kim
steps
`[16,8,4] -> [18,9,4] -> [20,10,4] -> [22,11,6] -> [24,12,8]`, including
complete weight distributions and literal row-space reconstruction at every
level.

The GF(13) repeated-lineage checker supplies two additional Table 1 rows. It
verifies the exact inverse pair
`[18,9,8] <-> [20,10,10]`, including normalized Kim--Lee presentations,
row-space reconstruction, complete weight distributions, and the exhaustive
audit of all 380 ordered two-coordinate reductions of the fixed length-20
code.

The GF(5) top-edge checker supplies the `[22,11,8] -> [24,12,9]` rows of
Table 1 and verifies the largest repeated box over that field.

The exact rank-one-obstruction audit is compiled and replayed with:

```sh
clang++ -O3 -std=c++17 \\
  Formalization/Verification/Examples/rank_one_obstruction_audit.cpp \\
  -o .lake/build/bin/rank_one_obstruction_audit
.lake/build/bin/rank_one_obstruction_audit 4
.lake/build/bin/rank_one_obstruction_audit 5
```

It enumerates all 28,800 systematic Euclidean self-dual generators of length
8 and all 18,720,000 of length 10 over `GF(5)`, together with all 1,680 and
30,240 oriented coordinate pairings, respectively. Every code has an `r=1`
pairing. Thus a permutation-invariant rank-two example cannot occur at either
length; the displayed rank-two example in the manuscript remains
pairing-dependent unless a larger certified obstruction is found.

The independent SAT replay
`python3 Formalization/Verification/Examples/rank_one_pairing_sat.py`
uses the project-local CaDiCaL 3.0.0 binary. Its 316-variable, 2,437-clause
instance selects an oriented perfect matching and a nonzero vector in the
boxed intersection. For the current Example 3.1 code it returns the
zero-based pairing `(0,2),(1,6),(4,3),(7,5)` with defect rank 3 and hence
`r=1`, independently confirming that the example is not a
permutation-invariant obstruction.

The separate `gf5_bklc_seed_audit.m` replay checks Magma's general linear-code
BKLC entries at `[20,10]`, `[22,11]`, and `[24,12]` over `GF(5)`. Their
distances are 8, 8, and 9, respectively, but none of the returned codes is
Euclidean self-dual. Thus BKLC is a useful distance bound and construction
baseline, not a direct source of self-dual parents without an additional
self-duality or diagonal-scaling test. Magma's BKLC tables do not cover
`GF(13)`.

The large Python check verifies all 3,432 seven-column information sets, performs
the exact universal normalization, enumerates the deletion parent, and checks
the fixed-parent lifting condition. The MDS deletion parent has exactly one
projective correction vector surviving the weight-six/seven filter. It also
generates the manuscript's block matrix and table row in
`large_applications_data.tex`.  The catalogue builder consumes that result and
generates `application_catalog_data.tex`.

The separate `gf13_mds_parent_ad_audit.m` replay enumerates all 36,036
minimum words of the `[14,7,8]` MDS code.  All 182 ordered two-coordinate
reductions give a parent with $A_6=960$, so changing only the deleted pair of
this fixed code cannot improve the Table 1 coefficient.

`LargeGF13.lean` separately kernel-checks the scalar Gram matrix, the
coordinate-reordered Gram matrix, the invertible row normalization in both
directions, the literal universal rank-one matrix, both universal Gram
relations, the exact deletion, and self-duality of the universal baseline and
its retained parent. The minimum-distance computation remains explicitly
external to Lean.
