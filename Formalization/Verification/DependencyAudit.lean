import Formalization.Archive.SubmittedBaseline
import Formalization.Sections.All

/-!
# Frozen-baseline declaration-dependency audit

The submitted monolithic file contains 260 theorem declarations.  This audit
computes which of them occur in the transitive declaration-dependency closure
of the paper-facing baseline API.  Dependency traversal includes both theorem
types and proof/definition values and passes through non-theorem declarations;
consequently, a theorem hidden behind a retained local definition is not
misclassified as unused.

The result is a deletion *candidate* set.  A declaration outside the closure is
not needed to kernel-check the retained paper roots, but may still be retained
as a historical Comparator benchmark.  The curated section modules decide
what is reviewer-facing.
-/

open Lean

private def pushNew (xs : Array Name) (n : Name) : Array Name :=
  if xs.contains n then xs else xs.push n

private def exprConsts (e : Expr) (init : Array Name := #[]) : Array Name :=
  e.foldConsts init fun n acc => pushNew acc n

private def declarationConsts (info : ConstantInfo) : Array Name :=
  let fromType := exprConsts info.type
  match info.value? (allowOpaque := true) with
  | some value => exprConsts value fromType
  | none => fromType

private def paperRoots : Array Name := #[
  -- Definitions and preliminary results explicitly exposed by the baseline.
  ``dot,
  ``dotBilin,
  ``rowSpace,
  ``paperSelfDualCode,
  ``paperLagrangianSubspace,
  ``paper_self_dual_iff_lagrangian,
  ``paper_dotBilin_nondegenerate,
  ``paperHyperbolicPair,
  ``splitE1,
  ``splitE2,
  ``split_seed_code_self_dual,
  ``dotBilin_nondegenerate,
  -- Binary paper interface.
  ``buildRowsBin_matrix_gram_zero,
  ``codeEquiv_rebuild_of_IsBoxedKimFamily,
  ``sameCode_boxedFamily_buildRowsBin,
  -- Split q-ary paper interface.
  ``buildRows_matrix_gram_zero,
  ``buildRows_rowSpace_self_dual_of_self_dual_parent_basis,
  ``splitBuildFamily_iff_rebuild,
  ``exists_unique_split_parent_of_IsSplitBuildFamily,
  ``exists_unique_splitBuildFamily_of_parent,
  ``exists_splitIsometryCodeEquiv_buildRows_of_pairwiseOrthogonal_isotropicHeadFamily,
  -- The seven wrappers in CurrentPaperTheoremSpine.
  ``paper_binary_kim_building_up_core,
  ``paper_binary_cz_kim_equivalence,
  ``paper_binary_boxed_equals_kim,
  ``paper_qary_building_up_rebuild,
  ``paper_qary_building_up_forward_self_dual,
  ``paper_split_boxed_form_forward_core,
  ``paper_conditional_split_boxed_normalization_core
]

private def modularPaperRoots : Array Name := #[
  ``BuildingUpFormalization.Components.Foundations.paperLagrangianSubspace_iff_totallyIsotropic_and_finrank_half,
  ``BuildingUpFormalization.Components.Foundations.paperSelfDualCode_iff_totallyIsotropic_and_finrank_half,
  ``BuildingUpFormalization.Components.Foundations.paperLagrangianSubspace_even_length,
  ``BuildingUpFormalization.Components.Foundations.paperSelfDualCode_even_length,
  ``BuildingUpFormalization.Components.Foundations.paper_systematic_form_criterion_exact,
  ``BuildingUpFormalization.Components.PermutationEquivalence.codeEquiv_preserves_paperSelfDualCode,
  ``BuildingUpFormalization.Components.NormForm.root_neg_one_orderOf,
  ``BuildingUpFormalization.Components.NormForm.paper_split_consequences_exact,
  ``BuildingUpFormalization.Components.NormForm.paper_euclidean_plane_hyperbolic_basis_exact,
  ``BuildingUpFormalization.Components.BinaryCzKim.paper_binary_kim_building_up_exact,
  ``BuildingUpFormalization.Components.BinaryCzKim.boxedFamily_tail_paperSelfDualCode,
  ``BuildingUpFormalization.Components.BinaryCzKim.paper_binary_cz_kim_corrected,
  ``BuildingUpFormalization.Components.QaryForward.paper_qary_kim_lee_building_up_exact,
  ``BuildingUpFormalization.Components.QaryForward.qaryAdaptedFamily_tail_paperSelfDualCode,
  ``BuildingUpFormalization.Components.QaryForward.paper_qary_adapted_reduction,
  ``BuildingUpFormalization.Components.QaryEquivalence.paper_qary_free_core_boxed_equivalence,
  ``BuildingUpFormalization.Components.SplitBoxed.splitBoxedRows_linearIndependent,
  ``BuildingUpFormalization.Components.SplitBoxed.splitBlockRowBilin_nondegenerate,
  ``BuildingUpFormalization.Components.SplitBoxed.splitBoxedRows_pairwiseOrthogonal,
  ``BuildingUpFormalization.Components.SplitBoxed.splitBoxedRows_rowSpace_selfDual,
  ``BuildingUpFormalization.Components.SplitBoxed.paper_split_boxed_form_exact
]

private def modularProofRepresentatives : Array Name := #[
  ``BuildingUpFormalization.Components.Foundations.paper_systematic_form_criterion_exact,
  ``BuildingUpFormalization.Components.PermutationEquivalence.codeEquiv_preserves_paperSelfDualCode,
  ``BuildingUpFormalization.Components.NormForm.paper_split_consequences_exact,
  ``BuildingUpFormalization.Components.BinaryCzKim.paper_binary_cz_kim_corrected,
  ``BuildingUpFormalization.Components.QaryForward.paper_qary_adapted_reduction,
  ``BuildingUpFormalization.Components.QaryEquivalence.paper_qary_free_core_boxed_equivalence,
  ``BuildingUpFormalization.Components.SplitBoxed.splitBlockRowBilin_nondegenerate,
  ``BuildingUpFormalization.Components.SplitBoxed.paper_split_boxed_form_exact
]

private partial def dependencyClosure
    (env : Environment) (localDecls : Array Name)
    (seen work : Array Name) : Array Name :=
  match work.back? with
  | none => seen
  | some n =>
      let work := work.pop
      if seen.contains n then
        dependencyClosure env localDecls seen work
      else
        let seen := seen.push n
        let work :=
          match env.find? n with
          | none => work
          | some info =>
              (declarationConsts info).foldl (init := work) fun acc dep =>
                if localDecls.contains dep && !seen.contains dep then
                  pushNew acc dep
                else
                  acc
        dependencyClosure env localDecls seen work

private def nameLt (a b : Name) : Bool := a.toString < b.toString

run_cmd do
  let env ← getEnv
  let some baselineModule := env.getModuleIdxFor? ``core_identity
    | throwError "cannot identify the BuildingUpFormalization module"
  let mut localDecls : Array Name := #[]
  let mut baselineTheorems : Array Name := #[]
  for (n, info) in env.constants do
    if env.getModuleIdxFor? n == some baselineModule then
      localDecls := localDecls.push n
      match info with
      | .thmInfo _ =>
          -- Source theorem declarations in the frozen file are all top-level;
          -- dotted names are compiler-generated equation lemmas/projections.
          if n.isAtomic then baselineTheorems := baselineTheorems.push n
      | _ => pure ()
  let closure := dependencyClosure env localDecls #[] paperRoots
  let retainedTheorems := baselineTheorems.filter closure.contains
  let candidates := baselineTheorems.filter fun n => !closure.contains n
  let sortedCandidates := candidates.qsort nameLt
  if baselineTheorems.size != 260 then
    throwError "expected 260 baseline theorems, found {baselineTheorems.size}"
  logInfo m!"BASELINE_THEOREMS={baselineTheorems.size}"
  logInfo m!"PAPER_ROOTS={paperRoots.size}"
  logInfo m!"LOCAL_DECLARATIONS_IN_CLOSURE={closure.size}"
  logInfo m!"THEOREMS_IN_PAPER_CLOSURE={retainedTheorems.size}"
  logInfo m!"THEOREMS_OUTSIDE_PAPER_CLOSURE={candidates.size}"
  for n in sortedCandidates do
    logInfo m!"OUTSIDE_PAPER_CLOSURE\t{n}"

run_cmd do
  let env ← getEnv
  let mut proofModules : Array ModuleIdx := #[]
  for representative in modularProofRepresentatives do
    let some moduleIdx := env.getModuleIdxFor? representative
      | throwError "cannot identify module for {representative}"
    if !proofModules.contains moduleIdx then
      proofModules := proofModules.push moduleIdx
  let mut localDecls : Array Name := #[]
  let mut modularTheorems : Array Name := #[]
  for (n, info) in env.constants do
    if n.toString.startsWith "BuildingUpFormalization.Components." then
      localDecls := localDecls.push n
    if let some moduleIdx := env.getModuleIdxFor? n then
      if proofModules.contains moduleIdx then
        match info with
        | .thmInfo _ =>
            -- Source declarations have exactly the three namespace prefixes
            -- plus the theorem name.  Longer names are compiler-generated.
            if (n.toString.splitOn ".").length == 4 then
              modularTheorems := modularTheorems.push n
        | _ => pure ()
  let closure := dependencyClosure env localDecls #[] modularPaperRoots
  let retainedTheorems := modularTheorems.filter closure.contains
  let candidates := modularTheorems.filter fun n => !closure.contains n
  let sortedCandidates := candidates.qsort nameLt
  if modularTheorems.size != 100 then
    throwError "expected 100 modular theorems, found {modularTheorems.size}"
  logInfo m!"MODULAR_THEOREMS={modularTheorems.size}"
  logInfo m!"MODULAR_PAPER_ROOTS={modularPaperRoots.size}"
  logInfo m!"MODULAR_THEOREMS_IN_PAPER_CLOSURE={retainedTheorems.size}"
  logInfo m!"MODULAR_THEOREMS_OUTSIDE_PAPER_CLOSURE={candidates.size}"
  for n in sortedCandidates do
    logInfo m!"MODULAR_OUTSIDE_PAPER_CLOSURE\t{n}"
