# Manuscript verification results

**PASS: complete Linux replay of 19 suites / 181 exact goals.**

The focused AFM revision snapshot was replayed on Linux on 2026-08-28. Every
Challenge/Solution suite passed statement and dependency comparison,
Comparator's sandbox, and Lean's default kernel. The same immutable input set
passed the production-token scan, full transitive-axiom audit, and the two
application computations retained in Section 4.

The complete receipt is
[`receipts/2026-08-28-afm-revision-181`](receipts/2026-08-28-afm-revision-181/README.md).
Its `summary.json` contains the 181 axiom reports, source and tool hashes,
dependency revisions, commands, exit statuses, and log hashes.

## Exact inventory

| Suite | Goals | Linux Comparator / default kernel |
|---|---:|---|
| BinaryCzKim | 18 | PASS / accepted |
| BinaryRankOneNormalization | 1 | PASS / accepted |
| BinaryTwoCoordinateReduction | 3 | PASS / accepted |
| ConditionalBoxed | 1 | PASS / accepted |
| Foundations | 22 | PASS / accepted |
| NormForm | 9 | PASS / accepted |
| PermutationEquivalence | 5 | PASS / accepted |
| QaryEquivalence | 1 | PASS / accepted |
| QaryForward | 21 | PASS / accepted |
| QaryRankBoxedNormalization | 2 | PASS / accepted |
| QaryRankOnePairingMerge | 51 | PASS / accepted |
| QaryRankOneUniversalPairing | 1 | PASS / accepted |
| RankBoxedExtension | 2 | PASS / accepted |
| RankBoxedStructure | 4 | PASS / accepted |
| RepeatedBox | 9 | PASS / accepted |
| RepeatedStep | 4 | PASS / accepted |
| SplitBoxed | 12 | PASS / accepted |
| SplitBoxedOrthogonality | 12 | PASS / accepted |
| SplitFormTransport | 3 | PASS / accepted |
| **Total** | **181** | **All accepted** |

## Trust boundary

- Lean `v4.29.0-rc6`; Mathlib
  `1f3cdaa7a7f82a2e521d285b11e261110e1e1962`.
- The 59 production dependency files contain no forbidden proof token.
- No Solution imports a Challenge; NanoDA is disabled.
- All exact goals depend only on `propext`, `Quot.sound`, and
  `Classical.choice`.
- Comparator SHA-256:
  `1b7b27b0233fd75672eeb777fec1c35257f1fb111acbb9cbcb2d0674a7b2c154`.
- lean4export SHA-256:
  `293e221ed1b515de1aeaf06d2fe8f3f919f0b75f1e4d3b228f43f53d576501ea`.
- landrun SHA-256:
  `6ada66a06669e8994e174a7271af2db636308e55a0d6ec896cc7d326b46727f6`.

The Chinburg--Zhang arithmetic existence theorem and the finite distance
enumerations remain explicit mathematical and computational inputs. The
separate reconstruction and arithmetic/four-coordinate follow-up are not part
of this 181-goal artifact.
