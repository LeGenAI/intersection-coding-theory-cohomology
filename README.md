# Building-Up Formalization Submission Package

This directory contains the submission package for the paper
`Formalizing the intersection of Coding Theory and Cohomology in Lean`.

The package is organized around a single Lean 4 development file,
`BuildingUpFormalization.lean`, together with the LaTeX source
`paper.tex` and the generated PDF `paper.pdf`.

## Scope

The formalized core covers the theorem spine of the current paper:

- self-dual and Lagrangian interfaces for Euclidean code spaces
- split hyperbolic background for fields with `q ≡ 1 (mod 4)`
- binary Kim building-up and the Chinburg–Zhang boxed comparison
- adapted split `q`-ary building-up
- split boxed forward theorem
- conditional reverse theorem up to split-isometric equivalence

The explicit GF(5) and GF(13) applications in the paper are supported by
external computation. Their mathematical interpretation appears in the
paper, but the searches and exhaustive distance checks are not part of the
Lean artifact.

## Pinned Environment

- Lean toolchain: `leanprover/lean4:v4.29.0-rc6`
- Lake: `5.0.0-src+00659f8`
- Mathlib: commit `1f3cdaa7a7f82a2e521d285b11e261110e1e1962`

The exact Mathlib commit is pinned in `lakefile.lean` and
`lake-manifest.json`. This artifact is intentionally maintained as a
paper-specific Lean development. It does **not** require any upstream merge
into Mathlib.

## Files

- `paper.tex`: current LaTeX source
- `paper.pdf`: current compiled paper
- `BuildingUpFormalization.lean`: single-file Lean development
- `BUILD.md`: reproducible build instructions
- `ARTIFACT_MAP.md`: paper-to-artifact map
- `SUBMISSION_CHECKLIST.md`: public release and AFM submission checklist

## Quick Start

To build the Lean artifact and the paper, see:

- [BUILD.md](./BUILD.md)
- [ARTIFACT_MAP.md](./ARTIFACT_MAP.md)

## Public Release Notes

For AFM submission, this package should be placed in a public repository or
public archive snapshot together with:

- a clear open-source license
- reproducible build instructions
- the pinned Lean/Mathlib versions already recorded here
- a permanent archive identifier for the paper preprint
- a Software Heritage identifier (SWHID) for the released code snapshot

The repository can remain completely independent of Mathlib upstream while
still satisfying these requirements.
