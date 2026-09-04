# Building-up constructions of self-dual codes

Revision artifact for *Formalizing building-up construction of self-dual
codes through isotropic lines in Lean*.

The public tree follows the focused AFM revision: binary building-up, the
split q-ary extension, and the universal rank-one normal form. Reconstruction
drafts and the separate arithmetic/four-coordinate follow-up are retained only
in the ignored `.internal/` workspace and are not part of this artifact.

## Contents

- `paper.tex`, `paper.pdf`, `AFM_buildingup_paper_v5.tex`,
  `AFM_buildingup_paper_v5.pdf`: current revision manuscript.
- `AFM_buildingup_response_to_referee_v4.pdf`: current response letter.
- `Formalization/Components/`: paper-facing definitions and completed proofs.
- `Formalization/Sections/`: section-level Lean entry points.
- `Formalization/Verification/Comparator/`: exactly 19 independent
  Challenge/Solution suites containing 181 declarations.
- `Formalization/Verification/Examples/`: the recursive GF(5) pair and the
  complete GF(13) repeated realization used in Section 4.
- `ARTIFACT_MAP.md`, `BUILD.md`: theorem map and reproducibility instructions.

Lean is pinned to `v4.29.0-rc6` and Mathlib to
`1f3cdaa7a7f82a2e521d285b11e261110e1e1962`. Production dependencies contain
no `sorry`, `admit`, user `axiom`, `sorryAx`, `native_decide`, or
`implemented_by`. The 181 exact goals use only `propext`, `Quot.sound`, and
`Classical.choice`; NanoDA is disabled.

## Reproduce

```sh
lake exe cache get
lake build
python3 comparator/verify_manuscript.py --output tmp/local-check
```

See [BUILD.md](BUILD.md) for the pinned Linux Comparator replay and PDF build,
and [RESULTS.md](Formalization/Verification/Comparator/RESULTS.md) for the
dated verification record.
