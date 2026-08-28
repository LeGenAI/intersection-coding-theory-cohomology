# Formalization archive

The current paper-facing API is provided by the section and component modules.
The frozen baseline below remains an imported dependency of the shared
definitions; archival placement does not mean it is absent from the build.

- `SubmittedBaseline.lean` is the frozen monolithic file submitted before the
  reviewer-driven section refactor. It is retained only because the modular
  revision imports shared definitions and lemmas from it. Historical
  cumulative Challenge generation and dependency-audit tooling are preserved
  in the ignored internal snapshot, not in the public revision tree.

New paper theorems belong under `Formalization/Components/` and are exposed
through `Formalization/Sections/`.  Nothing in this archive should be cited as
the current paper-facing theorem API.
