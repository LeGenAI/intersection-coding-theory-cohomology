# Formalization archive

The current paper-facing API is provided by the section and component modules.
The frozen baseline below remains an imported dependency of the shared
definitions; archival placement does not mean it is absent from the build.

- `SubmittedBaseline.lean` is the frozen 260-theorem file submitted before the
  reviewer-driven section refactor.  It is kept intact so the historical 260
  cumulative Comparator challenges remain reproducible.
- `Formalization.Verification.DependencyAudit` identifies the precise paper
  dependency closure.  Of the 260 submitted theorems, 158 occur in that
  closure and 102 do not in that historical audit. This is a declaration-level
  result, not a claim that those declarations have been removed from the
  imported baseline module.

New paper theorems belong under `Formalization/Components/` and are exposed
through `Formalization/Sections/`.  Nothing in this archive should be cited as
the current paper-facing theorem API.
