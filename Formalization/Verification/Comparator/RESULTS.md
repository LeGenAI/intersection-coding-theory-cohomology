# Manuscript verification results

**PASS: fresh complete Linux replay of 17 suites / 123 exact goals.**

The run started 2026-08-26 18:07:15 UTC and ended 18:15:37 UTC
(2026-08-27, 02:07--02:15 UTC+8).
All 17 suites were replayed in one fresh project snapshot. This supersedes
the earlier incremental 113 + 10 coverage; it is not merely a recount of
historical receipts.

## Evidence

- [Machine-readable summary and 105 input hashes](receipts/2026-08-27-afm-final/summary.json)
- [123 transitive axiom reports](receipts/2026-08-27-afm-final/axioms.log)
- [Section and Solution build](receipts/2026-08-27-afm-final/build.log)
- [Four rank-two GF(5) kernel certificates](receipts/2026-08-27-afm-final/rank-two-gf5.log)
- [Five exhaustive application computations](receipts/2026-08-27-afm-final/applications.log)

The summary records all 22 commands, exit statuses and log hashes.
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
| QaryRankBoxedNormalization | 1 | PASS / accepted |
| RankBoxedStructure | 3 | PASS / accepted |
| RankBoxedExtension | 1 | PASS / accepted |
| RepeatedStep | 4 | PASS / accepted |
| RepeatedBox | 6 | PASS / accepted |
| SplitBoxed | 12 | PASS / accepted |
| NormForm | 9 | PASS / accepted |
| SplitBoxedOrthogonality | 12 | PASS / accepted |
| BinaryTwoCoordinateReduction | 3 | PASS / accepted |
| SplitFormTransport | 3 | PASS / accepted |
| ConditionalBoxed | 1 | PASS / accepted |
| **Total** | **123** | **All accepted** |

Each suite's raw log is named `comparator-<Suite>.log` in the evidence directory.

## Trust boundary

- Lean `v4.29.0-rc6`; Mathlib
  `1f3cdaa7a7f82a2e521d285b11e261110e1e1962`.
- All nine dependency repositories matched the lockfile revisions and had
  clean tracked source trees; their existing package caches were reused.
- All 123 exact goals report only `propext`, `Classical.choice` and `Quot.sound`.
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

The four concrete rank-two certificates are separate from the 123 Comparator
goals. The five application distance computations are external exact finite
enumerations, not Lean proofs. Their input, generated TeX and complete weight
distributions are versioned under `../Examples/`.

The cited arithmetic realization theorem and separate arithmetic follow-up
are not claimed as conclusions of this AFM artifact.

See [BUILD.md](../../../BUILD.md) to reproduce the run and
[ARTIFACT_MAP.md](../../../ARTIFACT_MAP.md) for current theorem numbers.
