# Reproducible examples

The small application matrices catalogued by the manuscript are checked with:

```sh
python3 Formalization/Verification/Examples/check_applications.py --check
python3 Formalization/Verification/Examples/check_golay_lineage.py --check
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

The binary Golay checker supplies the separate lineage table.  It reduces the
standard extended Golay generator four times and verifies the exact inverse Kim
steps
`[16,8,4] -> [18,9,4] -> [20,10,4] -> [22,11,6] -> [24,12,8]`, including
complete weight distributions and literal row-space reconstruction at every
level.

The large Python check verifies all 3,432 seven-column information sets, performs
the exact universal normalization, enumerates the deletion parent, and checks
the fixed-parent lifting condition. The MDS deletion parent has exactly one
projective correction vector surviving the weight-six/seven filter. It also
generates the manuscript's block matrix and table row in
`large_applications_data.tex`.  The catalogue builder consumes that result and
generates `application_catalog_data.tex`.

`LargeGF13.lean` separately kernel-checks the scalar Gram matrix, the
coordinate-reordered Gram matrix, the invertible row normalization in both
directions, the literal universal rank-one matrix, both universal Gram
relations, the exact deletion, and self-duality of the universal baseline and
its retained parent. The minimum-distance computation remains explicitly
external to Lean.
