# Revision application checks

This directory contains only the computations used in Section 4 of the AFM
revision.

```sh
python3 Formalization/Verification/Examples/check_applications.py --check
python3 Formalization/Verification/Examples/check_gf13_repeated_lineage.py --check
```

`check_applications.py` verifies the recursive GF(5) pair: full row rank, zero
Gram matrix, complete weight distributions, MacWilliams identities, and the
literal reductions `[4,2,2] -> [6,3,4] -> [8,4,4]`.

`check_gf13_repeated_lineage.py` reconstructs the displayed GF(13)
`[20,10,10]` child from its `[18,9,8]` rank-one parent. It verifies the
two-coordinate reduction, the normalized parent, the correction-vector
relations, literal Kim--Lee reconstruction, row-space equality, complete
weight distributions, and the generated TeX matrix. The independent Magma
receipt records the exhaustive audit of all 380 ordered coordinate pairs.

The calculations are exact finite computations and are not represented as
Lean proofs.
