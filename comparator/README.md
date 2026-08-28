# Revision verification runner

`verify_manuscript.py` is the authoritative verifier for the focused AFM
artifact. It selects an explicit immutable list of 19 modular Comparator
suites containing 181 exact declarations; unrelated JSON files cannot inflate
the inventory through directory globbing.

Run a local Lean, trust, axiom, and application audit with:

```sh
python3 comparator/verify_manuscript.py --output tmp/local-check
```

For the pinned Linux Comparator replay, supply all three binaries as described
in [BUILD.md](../BUILD.md). The output directory must be new.

The former cumulative 260-hole generator is retained only in the ignored
internal snapshot. It is not part of the public revision or verification path.
