# Build and verification

## Pinned environment

- Lean: `leanprover/lean4:v4.29.0-rc6`
- Mathlib: `1f3cdaa7a7f82a2e521d285b11e261110e1e1962`
- Python: 3.9 or newer, standard library only
- PDF engine: Tectonic; Menlo, DejaVu Sans Mono or Latin Modern Mono

From a fresh checkout with elan/Lake installed:

```sh
lake exe cache get
lake build
```

The default target imports only the manuscript section API and its dependencies.
The archived baseline is still required by shared definitions. No separate
arithmetic-research modules are needed.

## Current manuscript audit

```sh
python3 comparator/verify_manuscript.py --output tmp/local-check
```

This builds the 17 Solutions, checks their local import closure for forbidden
proof tokens, verifies dependency revisions and clean tracked dependency
sources, and prints the transitive axioms of all 123 exact goals. It also
compiles the rank-two GF(5) certificates and reruns the application catalogue,
the large GF(13) computation, and the length-20-centered binary Golay lineage. The output
directory must be new. A local audit is not a Comparator replay.

## Linux Comparator replay

Build Comparator at commit
`a4f696825c583ed8a5b4060d9a0faa5b882d365b` and use its compatible
Lean-4.29 exporter and real landrun. The recorded binary hashes are enforced by
the runner; all three binaries must match the recorded environment.

```sh
python3 comparator/verify_manuscript.py --output linux-check \
  --comparator /path/to/comparator \
  --lean4export /path/to/lean4export \
  --landrun /path/to/landrun
```

This replays every suite, with NanoDA disabled and the default kernel enabled.
The output includes the input hashes, tool hashes, per-step logs, dependency
revisions and all axiom reports. Do not replace a pinned binary silently.
For an independently built binary with a different hash, document the build
and run the JSON suites directly; do not describe it as the recorded replay.

## Numerical applications

```sh
python3 Formalization/Verification/Examples/check_applications.py --check
python3 Formalization/Verification/Examples/check_large_applications.py --check
python3 Formalization/Verification/Examples/check_golay_lineage.py --check
python3 Formalization/Verification/Examples/check_gf13_repeated_lineage.py --check
python3 Formalization/Verification/Examples/build_application_catalog.py --check
```

`applications.json` is the single input for all five application matrices,
parameters and witness words. The checker verifies Gram relations, full rank,
complete weight distributions, the MacWilliams identity and two GF(5)
reductions. Negative-control tests reject the two corrected GF(13) coefficients.
After an intentional data change, use `--write` to regenerate
`applications_data.tex` and `applications_results.json`, then run `--check`.
The script enumerates 4,826,808 nonzero vectors in its largest example.
These computations are not Lean proofs.

`check_golay_lineage.py` starts from the standard extended binary Golay
generator, performs four exact two-coordinate reductions, and completely
enumerates every code from `[24,12,8]` down to `[16,8,4]`. At all four edges it
checks rank, Gram matrix, the MacWilliams identity, the Kim coefficient
relations, literal reconstruction, and equality of the reconstructed and child
row spaces. Its generated table rows and certificate are versioned with the
manuscript.

The GF(13) repeated-lineage checker starts from the published pure
double-circulant [22,11,10] code, checks the two exact reductions through
[20,10,8] to [18,9,7], and verifies both inverse Kim--Lee matrices. It also
checks the supplied complete Magma weight distributions at lengths 20 and 18
against the MacWilliams identity.

`build_application_catalog.py` does not recompute distances. It packages the
two verified result files into the reviewer-facing `application_catalog.json`,
seven individual certificates, and the generated Table 1 rows. After an
intentional numerical-data change, run the two numerical checkers with
`--write`, then the catalogue builder with `--write`, and finish with all three
`--check` commands.

The separate rank-two [8,4] -> [10,5] -> [12,6] example is checked by:

```sh
lake env lean Formalization/Verification/Examples/RankTwoGF5.lean
```

## Historical baseline

The frozen baseline's 260 cumulative single-hole Challenges can be regenerated:

```sh
python3 comparator/generate_challenge.py
python3 comparator/generate_challenge.py --check
```

These historical challenges are not the current 123-goal inventory.

## PDF

```sh
tectonic --keep-intermediates --keep-logs paper.tex
```

This overwrites `paper.pdf`. Generated application TeX is versioned and
verified separately. The response letter is private submission correspondence,
not part of this public artifact; when present locally, build it after
`paper.tex` so that its imported theorem labels are current.
