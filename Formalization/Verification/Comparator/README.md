# Independent theorem comparisons

Each JSON configuration pairs a statement-side Challenge with a completed
Solution. All 17 suites permit only `propext`, `Quot.sound` and
`Classical.choice`; NanoDA is disabled and Lean default-kernel replay is enabled.
Challenges intentionally contain proof placeholders. A Solution must not import
a Challenge, and no completed proof may depend on `sorryAx`.

The 126 distinct declarations include the universal q-ary and binary goals,
the exact building-up iff, same-D recursive restriction and extension, and
both fixed-parent directions of the repeated-box/Kim--Lee correspondence.
The zero correction column is treated explicitly as a direct-sum case.

Run one configuration from the project root:

```sh
lake env /path/to/comparator Formalization/Verification/Comparator/Foundations.json
```

For the pinned full replay, use `comparator/verify_manuscript.py` as described
in [BUILD.md](../../../BUILD.md). The [result record](RESULTS.md) gives
the execution scope and links to raw evidence.
[ARTIFACT_MAP.md](../../../ARTIFACT_MAP.md) maps current theorem numbers
to stable Lean names.

The binary arithmetic wrapper does not prove the cited arithmetic realization
theorem. The distance computations are external certificates. Neither is
silently included in the 126-goal count.
