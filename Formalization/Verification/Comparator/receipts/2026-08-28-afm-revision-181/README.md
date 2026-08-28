# Focused AFM revision replay

This directory records the complete Linux replay of the focused revision
snapshot on 2026-08-28.

- 19 independent Challenge/Solution suites
- 181 distinct exact declarations
- Lean build and default-kernel acceptance: PASS
- Comparator sandbox replay: PASS for every suite
- transitive axiom coverage: 181/181, with only `propext`, `Quot.sound`, and
  `Classical.choice`
- production dependency scan: no `sorry`, `admit`, user `axiom`, `sorryAx`,
  `native_decide`, or `implemented_by`
- revision application computations: PASS

`summary.json` records the input hashes, dependency revisions, pinned tool
hashes, step exit codes, log hashes, and every axiom report. The 19
`comparator-*.log` files end with both default-kernel acceptance and
`Your solution is okay!`.
