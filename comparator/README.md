# Building-up Comparator generation

The authoritative frozen source is `../Formalization/Archive/SubmittedBaseline.lean`. The
generator creates one cumulative Comparator challenge for each of all 260
top-level theorems, including the four declarations carrying an inline
`@[simp]` attribute.

From the repository root, regenerate and check the artifacts with:

```sh
python3 comparator/generate_challenge.py
python3 comparator/generate_challenge.py --check
```

Generated files live in `ComparatorChallenges/BuildingUp`. The shared Solution
is a byte-for-byte copy of the authoritative source. Each Challenge preserves
the exact source prefix and all earlier proofs, replaces only its target
theorem proof with `by sorry`, omits later declarations, and closes the active
sections. This prevents later theorems from leaking into an earlier challenge
and keeps proof-valued dependencies identical under Comparator.

The ordered module/config inventory is `theorems.tsv`. Use a Comparator and
`lean4export` built for Lean `v4.29.0-rc6`. For example, compile and compare the
first challenge with:

```sh
lake env lean ComparatorChallenges/BuildingUp/AllTheorems/T001CoreIdentityChallenge.lean
lake env lean ComparatorChallenges/BuildingUp/BuildingUpAllSolution.lean
lake env /path/to/comparator ComparatorChallenges/BuildingUp/AllTheorems/T001CoreIdentity.json
```
