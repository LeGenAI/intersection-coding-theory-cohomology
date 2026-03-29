# Artifact Map

This file records the correspondence between the current paper and the Lean
artifact.

## Core Files

- Paper source: `paper.tex`
- Paper PDF: `paper.pdf`
- Lean artifact: `BuildingUpFormalization.lean`

## Formalized vs. External

### Formalized in Lean

- self-dual / Lagrangian interface
- nondegeneracy of the Euclidean bilinear form
- split hyperbolic background
- binary Kim building-up interface
- binary Chinburg–Zhang / Kim equivalence theorem
- adapted split `q`-ary building-up theorem
- split boxed forward theorem
- conditional reverse theorem up to split-isometric equivalence

### External Computation

- exhaustive GF(5) classification outputs
- explicit GF(13) code searches
- external minimum-distance computations for application examples

## Paper-to-Lean Map

### Preliminaries

- Definitions `self-dual code`, `Lagrangian subspace`
  - `paperSelfDualCode`
  - `paperLagrangianSubspace`
  - `paper_self_dual_iff_lagrangian`
  - `paper_dotBilin_nondegenerate`

- Split hyperbolic preliminaries
  - `paperHyperbolicPair`
  - `splitE1`
  - `splitE2`

### Binary Section

- Theorem `thm:binary-cz-kim` / `thm:CZ_Kim_Lagrangian`
  - `paper_binary_cz_kim_equivalence`
  - `boxedFamily_eq_buildRowsBin`
  - `deleteHyperbolicPair_buildRowsBin`

### Split q-ary Section

- Theorem `thm:qary-building-up`
  - `paper_qary_building_up_rebuild`
  - `paper_qary_building_up_forward_self_dual`
  - `splitBuildFamily_iff_rebuild`
  - `exists_unique_split_parent_of_IsSplitBuildFamily`

- Theorem `thm:split-boxed-form`
  - `paper_split_boxed_form_forward_core`

- Theorem `thm:conditional-split-boxed-normalization`
  - `paper_conditional_split_boxed_normalization_core`

## Verification Status

Whole-file AXLE check:

- `okay: true`
- `failed_declarations: []`
- `error_count: 0`

Theorem-level AXLE verification was run for the paper-facing wrappers in the
binary and split `q`-ary theorem spine.
