# Independent theorem comparisons

The directory contains exactly 19 paper-facing JSON configurations. Each
configuration pairs a statement-only Challenge with a completed Solution and
lists its exact theorem names. Together they contain 181 distinct declarations.

All suites disable NanoDA and permit only `propext`, `Quot.sound`, and
`Classical.choice`. Challenges intentionally contain proof placeholders;
Solutions never import Challenges, and their complete production dependency
closure is scanned for `sorry`, `admit`, user `axiom`, `sorryAx`,
`native_decide`, and `implemented_by`.

Run one suite from the project root with:

```sh
lake env /path/to/comparator Formalization/Verification/Comparator/Foundations.json
```

Use `comparator/verify_manuscript.py` for the complete local audit or pinned
Linux replay. See [BUILD.md](../../../BUILD.md) and
[RESULTS.md](RESULTS.md).

The arithmetic existence theorem cited from Chinburg--Zhang and the finite
distance computations are explicit external inputs. Separate arithmetic and
four-coordinate follow-up work is not included in these 181 goals.
