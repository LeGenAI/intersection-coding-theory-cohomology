# Building-up constructions of self-dual codes

Lean 4 artifact accompanying *Formalizing building-up construction of self-dual
codes through isotropic lines in Lean*.

The manuscript proves universal rank-r boxed representations over split odd
fields, recursive restrictions and extensions, a fixed-parent correspondence
with Kim--Lee building-up, and an independent binary rank-one normalization.
It distinguishes these algebraic results from the cited arithmetic realization
theorem of Chinburg--Zhang.

## Artifact layout

- `paper.tex`, `paper.pdf`: manuscript and compiled PDF.
- `Formalization.lean`: default entry point importing the section API.
- `Formalization/Sections/`: mathematical section entry points.
- `Formalization/Components/`: definitions and proofs.
- `Formalization/Archive/SubmittedBaseline.lean`: frozen baseline supplying
  shared infrastructure; its 260 theorems are not additional current exact goals.
- `Formalization/Verification/Comparator/`: 17 independent suites / 124 goals.
- `Formalization/Verification/Examples/`: kernel-checked rank-two example,
  reproducible application data, a public historical catalogue, the exact
  length-20-centered Golay lineage, linked certificates, generators and complete weight
  distributions.
- `comparator/verify_manuscript.py`: current build, trust audit and Linux replay.
- `ARTIFACT_MAP.md`, `BUILD.md`: theorem map and reproduction instructions.

Lean is pinned to `v4.29.0-rc6`; Mathlib is pinned to
`1f3cdaa7a7f82a2e521d285b11e261110e1e1962`.
The only permitted foundational axioms are `propext`, `Quot.sound` and
`Classical.choice`. NanoDA is disabled. Placeholder proofs occur only in
statement-side Challenges, not in completed Solutions or their proof dependencies.

## Reproduce

```sh
lake exe cache get
lake build
python3 comparator/verify_manuscript.py --output tmp/local-check
python3 Formalization/Verification/Examples/check_applications.py --check
python3 Formalization/Verification/Examples/check_large_applications.py --check
python3 Formalization/Verification/Examples/check_golay_lineage.py --check
python3 Formalization/Verification/Examples/check_gf5_repeated_top.py --check
python3 Formalization/Verification/Examples/check_gf13_repeated_lineage.py --check
python3 Formalization/Verification/Examples/build_application_catalog.py --check
```

The verification output directory must not already exist.
See [BUILD.md](BUILD.md) for the full procedure and
[RESULTS.md](Formalization/Verification/Comparator/RESULTS.md) for dated evidence.
The finite-field distance computations are not Lean proofs.
