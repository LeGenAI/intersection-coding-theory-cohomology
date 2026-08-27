# Manuscript verification results

**PASS: fresh complete Linux replay of 17 suites / 126 exact goals.**

The current run started 2026-08-27 08:23:04 UTC and ended 08:30:48 UTC
(2026-08-27, 16:23--16:30 UTC+8).
All 17 suites were replayed in one fresh project snapshot. This supersedes
the earlier full replay as well as the incremental 113 + 10 coverage; it is
not merely a recount of historical receipts.

## Evidence

- [Machine-readable summary and 139 input hashes](receipts/2026-08-27-minimal-form-linux-final2/summary.json)
- [126 transitive axiom reports](receipts/2026-08-27-minimal-form-linux-final2/axioms.log)
- [Section and Solution build](receipts/2026-08-27-minimal-form-linux-final2/build.log)
- [Four rank-two GF(5) kernel certificates](receipts/2026-08-27-minimal-form-linux-final2/rank-two-gf5.log)
- [Finite-field application computations](receipts/2026-08-27-minimal-form-linux-final2/applications.log)
- [Large GF(13) computation](receipts/2026-08-27-minimal-form-linux-final2/large-applications.log)
- [Binary Golay descent, ascent and universal parent](receipts/2026-08-27-minimal-form-linux-final2/golay-lineage.log)
- [GF(5) Corollary 3.10 parent](receipts/2026-08-27-minimal-form-linux-final2/gf5-repeated-top.log)
- [GF(13) Corollary 3.10 parent](receipts/2026-08-27-minimal-form-linux-final2/gf13-repeated-lineage.log)
- [Generated historical catalogue](receipts/2026-08-27-minimal-form-linux-final2/application-catalogue.log)

The summary records all 28 commands, exit statuses and log hashes.
Every input hash was checked again after execution, and all input and log
hashes were verified after retrieval. The same source snapshot passed the
local build, transitive axiom audit, rank-two certificate check and computations.

## Exact goal inventory

| Suite | Goals | Linux Comparator / default kernel |
|---|---:|---|
| Foundations | 22 | PASS / accepted |
| BinaryCzKim | 18 | PASS / accepted |
| PermutationEquivalence | 5 | PASS / accepted |
| QaryForward | 21 | PASS / accepted |
| QaryEquivalence | 1 | PASS / accepted |
| BinaryRankOneNormalization | 1 | PASS / accepted |
| QaryRankBoxedNormalization | 2 | PASS / accepted |
| RankBoxedStructure | 3 | PASS / accepted |
| RankBoxedExtension | 2 | PASS / accepted |
| RepeatedStep | 4 | PASS / accepted |
| RepeatedBox | 7 | PASS / accepted |
| SplitBoxed | 12 | PASS / accepted |
| NormForm | 9 | PASS / accepted |
| SplitBoxedOrthogonality | 12 | PASS / accepted |
| BinaryTwoCoordinateReduction | 3 | PASS / accepted |
| SplitFormTransport | 3 | PASS / accepted |
| ConditionalBoxed | 1 | PASS / accepted |
| **Total** | **126** | **All accepted** |

Each suite's raw log is named `comparator-<Suite>.log` in the evidence directory.

## Trust boundary

- Lean `v4.29.0-rc6`; Mathlib
  `1f3cdaa7a7f82a2e521d285b11e261110e1e1962`.
- All nine dependency repositories matched the lockfile revisions and had
  clean tracked source trees; their existing package caches were reused.
- All 126 exact goals report only `propext`, `Classical.choice` and `Quot.sound`.
- The 53 local production dependency files contain no executable
  `sorry`, `admit`, user `axiom`, `sorryAx`, `native_decide` or
  `implemented_by`. The scanner masks nested comments and strings.
- No Solution imports a Challenge. Statement-side placeholders are intentional.
- NanoDA is disabled; all runs use real landrun and Lean default-kernel replay.
- Comparator SHA-256:
  `1b7b27b0233fd75672eeb777fec1c35257f1fb111acbb9cbcb2d0674a7b2c154`.
- Compatible lean4export SHA-256:
  `293e221ed1b515de1aeaf06d2fe8f3f919f0b75f1e4d3b228f43f53d576501ea`.
- Real landrun SHA-256:
  `6ada66a06669e8994e174a7271af2db636308e55a0d6ec896cc7d326b46727f6`.

Existing linter warnings and extra blank lines at the ends of frozen proof
files are retained to preserve their certified bytes; they are not failed goals.

## Scope

The universal normal-form goals require actual row-space equality with the
given code after the stated coordinate permutation. The repeated-step goals
include the nonzero-correction iff and the zero-correction direct-sum case.

The concrete rank-two certificates and finite-code computations are separate
from the 126 Comparator goals. The application distances and the two-step
Golay lineage are external exact finite enumerations, not Lean proofs. Their
inputs, generated TeX, reconstruction certificates and complete weight
distributions are versioned under `../Examples/`.  The largest binary parent
is oriented with zero pivot diagonal as in Theorem 3.8; the largest GF(5) and
GF(13) parents are normalized literally to the rank-one form of Corollary 3.10.
The generic deletion and
rebuilding equality used at each Golay step is the exact BinaryCzKim goal.

The cited arithmetic realization theorem and separate arithmetic follow-up
are not claimed as conclusions of this AFM artifact.

See [BUILD.md](../../../BUILD.md) to reproduce the run and
[ARTIFACT_MAP.md](../../../ARTIFACT_MAP.md) for current theorem numbers.
