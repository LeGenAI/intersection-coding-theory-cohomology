# Modular Lean layout

`Components/` contains paper-facing definitions and completed proofs;
`Sections/` follows the binary, split q-ary, and universal order of Section 3;
`Verification/Comparator/` contains the independent exact comparisons.

| Suite | Goals |
|---|---:|
| Foundations | 22 |
| PermutationEquivalence | 5 |
| NormForm | 9 |
| BinaryCzKim | 18 |
| BinaryRankOneNormalization | 1 |
| QaryRankBoxedNormalization | 2 |
| QaryRankOnePairingMerge | 51 |
| QaryRankOneUniversalPairing | 1 |
| RankBoxedStructure | 4 |
| RankBoxedExtension | 2 |
| RepeatedStep | 4 |
| RepeatedBox | 9 |
| QaryForward | 21 |
| QaryEquivalence | 1 |
| SplitBoxed | 12 |
| SplitBoxedOrthogonality | 12 |
| BinaryTwoCoordinateReduction | 3 |
| SplitFormTransport | 3 |
| ConditionalBoxed | 1 |
| **Total** | **181** |

Each suite has a JSON configuration, statement-only Challenge, completed
Solution, and transitive axiom audit. `Formalization.Sections.All` is the
curated entry point. `Archive/SubmittedBaseline.lean` remains only because
shared definitions depend on it; its historical 260 declarations are not 260
additional current Challenge/Solution goals.

The production import closure contains no executable `sorry`, `admit`, user
`axiom`, `sorryAx`, `native_decide`, or `implemented_by`. All exact goals use
only `propext`, `Quot.sound`, and `Classical.choice`. The public AFM artifact
does not include the separate arithmetic or four-coordinate follow-up.
