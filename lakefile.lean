import Lake
open Lake DSL

package «buildingup-paper-submission» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "1f3cdaa7a7f82a2e521d285b11e261110e1e1962"

/-- Modular components, section entry points, and verification modules. -/
@[default_target]
lean_lib Formalization where
  srcDir := "."

/-- Generated statement-only modules consumed by Comparator. -/
lean_lib ComparatorChallenges where
  srcDir := "."
