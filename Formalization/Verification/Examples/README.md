# Reproducible examples

The small application matrices printed in the manuscript are checked with:

```sh
python3 Formalization/Verification/Examples/check_applications.py --check
```

The first large-application baseline starts from the known pure
double-circulant self-dual MDS `[14,7,8]` code over `GF(13)` and runs:

```sh
python3 Formalization/Verification/Examples/check_large_applications.py --check
lake env lean Formalization/Verification/Examples/LargeGF13.lean
```

The Python check verifies all 3,432 seven-column information sets, performs
the exact universal normalization, enumerates the deletion parent, and checks
the fixed-parent lifting condition. The MDS deletion parent has exactly one
projective correction vector surviving the weight-six/seven filter. It also
generates the manuscript's block matrix and table row in
`large_applications_data.tex`.

`LargeGF13.lean` separately kernel-checks the scalar Gram matrix, the
coordinate-reordered Gram matrix, the invertible row normalization in both
directions, the literal universal rank-one matrix, both universal Gram
relations, the exact deletion, and self-duality of the universal baseline and
its retained parent. The minimum-distance computation remains explicitly
external to Lean.
