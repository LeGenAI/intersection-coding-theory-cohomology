# Build and verification

## Pinned environment

- Lean `v4.29.0-rc6`
- Mathlib `1f3cdaa7a7f82a2e521d285b11e261110e1e1962`
- Python 3.9 or newer, standard library only
- Tectonic for the PDFs

From a fresh checkout:

```sh
lake exe cache get
lake build
```

The archived submitted baseline remains a proof dependency for shared
definitions. Its former cumulative 260-hole generator is not part of the
revision inventory; the current inventory is the 19 modular suites below.

## Manuscript audit

```sh
python3 comparator/verify_manuscript.py --output tmp/local-check
```

The output directory must not already exist. The runner builds all 19
Solutions, checks the complete production import closure for forbidden proof
tokens, verifies the pinned dependency revisions, prints the transitive axioms
of all 181 declarations, and reruns precisely the two application computations
used in Section 4:

```sh
python3 Formalization/Verification/Examples/check_applications.py --check
python3 Formalization/Verification/Examples/check_gf13_repeated_lineage.py --check
```

The first command checks the GF(5) chain
`[4,2,2] -> [6,3,4] -> [8,4,4]`. The second checks the exact GF(13)
`[18,9,8] <-> [20,10,10]` reduction and Kim--Lee reconstruction, together
with the supplied complete weight distributions and their MacWilliams
identities. These finite computations are reproducible certificates, not Lean
proofs.

## Linux Comparator replay

Use Comparator commit `a4f696825c583ed8a5b4060d9a0faa5b882d365b`
with binaries matching the hashes enforced by `verify_manuscript.py`:

```sh
python3 comparator/verify_manuscript.py --output linux-check \
  --comparator /path/to/comparator \
  --lean4export /path/to/lean4export \
  --landrun /path/to/landrun
```

This replays every JSON suite with NanoDA disabled and checks both Comparator's
sandbox and Lean's default kernel. The output records input, tool, dependency,
and log hashes plus all 181 axiom reports.

## PDFs

```sh
tectonic --keep-intermediates --keep-logs paper.tex
tectonic --keep-intermediates --keep-logs response_to_referee.tex
```

The versioned submission copies are `AFM_buildingup_paper_v3.pdf` and
`AFM_buildingup_response_to_referee_v2.pdf`.
