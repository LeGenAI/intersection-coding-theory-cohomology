# Submission Checklist

This checklist is aimed at an AFM-style submission package.

## Repository Release

- [ ] Create a public repository for `paper_submission`
- [ ] Add an open-source license
- [ ] Commit:
  - `paper.tex`
  - `paper.pdf`
  - `BuildingUpFormalization.lean`
  - `lakefile.lean`
  - `lake-manifest.json`
  - `lean-toolchain`
  - `README.md`
  - `BUILD.md`
  - `ARTIFACT_MAP.md`
- [ ] Exclude transient build outputs and local caches

## Public Preprint

- [ ] Upload the paper to arXiv, HAL, or Zenodo
- [ ] Record the permanent identifier in the repository README

## Reproducibility

- [ ] Confirm Lean toolchain version
- [ ] Confirm Mathlib commit matches:
  - `1f3cdaa7a7f82a2e521d285b11e261110e1e1962`
- [ ] Run `lake build`
- [ ] Run `tectonic paper.tex`
- [ ] Keep `BuildingUpFormalization.lean` as the authoritative single-file artifact

## AXLE / Proof Verification

- [ ] Whole-file AXLE check
- [ ] Verify the paper-facing theorem wrappers
- [ ] Save AXLE summaries if desired for referee support

## SWHID

SWHIDs are generated from a **public archived snapshot**. This cannot be
completed purely locally.

Release workflow:

1. Push the public repository
2. Ensure the repository is visible to Software Heritage
3. Create a stable release tag
4. Wait for archive ingestion
5. Record the resulting SWHID in the submission metadata and final paper

## Important Note

This submission package does **not** require any upstream merge into
Mathlib. The dependency is pinned to an external commit, and the artifact can
remain a standalone paper-specific development.
