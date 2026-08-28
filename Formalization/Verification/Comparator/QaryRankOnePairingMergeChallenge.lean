import Formalization.Components.QaryRankOnePairingMergeDefinitions
import Formalization.Components.RepeatedStepDefinitions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryRankOnePairingMerge

open Set Submodule
open BuildingUpFormalization.Components.QaryRankBoxedNormalization
open BuildingUpFormalization.Components.QaryRankOneOrientedPairing
open BuildingUpFormalization.Components.SplitBoxed
open BuildingUpFormalization.Components.RepeatedStep

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Exact dimension of the standard product of isotropic lines. -/
theorem finrank_qaryIsotropicLineCode_exact [Fintype ι] (c : K) :
    Module.finrank K ↥(qaryIsotropicLineCode (K := K) (ι := ι) c) =
      Fintype.card ι := by
  sorry

/-- Whole-block relabelling preserves the isotropic-line code. -/
theorem relabelBlockCode_qaryIsotropicLineCode_exact
    {κ : Type*} [Fintype ι] [Fintype κ]
    (c : K) (σ : ι ≃ κ) :
    relabelBlockCode (K := K) σ
        (qaryIsotropicLineCode (K := K) (ι := κ) c) =
      qaryIsotropicLineCode (K := K) (ι := ι) c := by
  sorry

/-- Whole-block relabelling preserves the isotropic intersection dimension. -/
theorem finrank_relabelBlockCode_inf_qaryIsotropicLineCode_exact
    {κ : Type*} [Fintype ι] [Fintype κ]
    (c : K) (σ : ι ≃ κ)
    (C : Submodule K (QaryBlockRow K κ)) :
    Module.finrank K
        ↥(relabelBlockCode (K := K) σ C ⊓
          qaryIsotropicLineCode (K := K) (ι := ι) c) =
      Module.finrank K
        ↥(C ⊓ qaryIsotropicLineCode (K := K) (ι := κ) c) := by
  sorry

/-- The identity scalar-coordinate permutation fixes every block code. -/
theorem scalarCoordinatePermutedBlockCode_refl_exact
    {n : ℕ} (C : Submodule K (QaryBlockRow K (Fin n))) :
    scalarCoordinatePermutedBlockCode (K := K)
      (Equiv.refl (Fin n × Fin 2)) C = C := by
  sorry

/-- Exact composition law for scalar-coordinate permutations. -/
theorem scalarCoordinatePermutedBlockCode_trans_exact
    {n : ℕ} (σ τ : Equiv.Perm (Fin n × Fin 2))
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    scalarCoordinatePermutedBlockCode (K := K) τ
        (scalarCoordinatePermutedBlockCode (K := K) σ C) =
      scalarCoordinatePermutedBlockCode (K := K) (σ.trans τ) C := by
  sorry

/-- Rank-one oriented pairing is invariant under scalar-coordinate
permutation of the code. -/
theorem hasQaryRankOneOrientedPairing_scalarCoordinatePermuted_iff
    {n : ℕ} (c : K) (σ : Equiv.Perm (Fin n × Fin 2))
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    HasQaryRankOneOrientedPairing c
        (scalarCoordinatePermutedBlockCode (K := K) σ C) ↔
      HasQaryRankOneOrientedPairing c C := by
  sorry

/-- A whole-block relabelling is the corresponding scalar-coordinate
permutation moving both entries of every block together. -/
theorem relabelBlockCode_eq_scalarCoordinatePermutedBlockCode_exact
    {n : ℕ} (σ : Equiv.Perm (Fin n))
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    relabelBlockCode (K := K) σ C =
      scalarCoordinatePermutedBlockCode (K := K)
        (blockRelabelScalarPerm σ) C := by
  sorry

/-- Rank-one oriented pairing is invariant under a whole-block
permutation. -/
theorem hasQaryRankOneOrientedPairing_relabelBlockCode_iff
    {n : ℕ} (c : K) (σ : Equiv.Perm (Fin n))
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    HasQaryRankOneOrientedPairing c (relabelBlockCode (K := K) σ C) ↔
      HasQaryRankOneOrientedPairing c C := by
  sorry

/-- Exact injectivity of the block Kim--Lee generator. -/
theorem kimLeeBlockGenerator_injective
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (ell : Module.Dual K C) :
    Function.Injective (kimLeeBlockGenerator (K := K) c C ell) := by
  sorry

/-- Exact defect formula for the block Kim--Lee generator. -/
theorem qaryBlockDefectLinear_kimLeeBlockGenerator_exact
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (ell : Module.Dual K C) (az : K × C) :
    qaryBlockDefectLinear (K := K) c
        (kimLeeBlockGenerator (K := K) c C ell az) =
      fun o => match o with
        | none => -c * az.1
        | some i => blockDefectLinear c ((az.2 : QaryBlockRow K ι) i) := by
  sorry

/-- Kim--Lee extension preserves the exact isotropic intersection dimension. -/
theorem kimLeeBlockCode_inf_qaryIsotropicLineCode_finrank_exact
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (ell : Module.Dual K C) (hc : c ^ 2 = (-1 : K)) :
    Module.finrank K
        ↥(kimLeeBlockCode (K := K) c C ell ⊓
          qaryIsotropicLineCode (K := K) (ι := Option ι) c) =
      Module.finrank K
        ↥(C ⊓ qaryIsotropicLineCode (K := K) (ι := ι) c) := by
  sorry

/-- Exact finite-index Kim--Lee rank-one induction step. -/
theorem finKimLeeBlockCode_has_rankOne_orientedPairing_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (ell : Module.Dual K C) (hc : c ^ 2 = (-1 : K))
    (hone : Module.finrank K
      ↥(C ⊓ qaryIsotropicLineCode (K := K) c) = 1) :
    HasQaryRankOneOrientedPairing c
      (finKimLeeBlockCode (K := K) c C ell) := by
  sorry

/-- Exact defect formula for the literal block form of `buildRows`. -/
theorem qaryBlockDefectLinear_buildingUpBlockGenerator_exact
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (x : QaryBlockRow K ι) (ell : Module.Dual K C) (az : K × C) :
    qaryBlockDefectLinear (K := K) c
        (buildingUpBlockGenerator (K := K) c C x ell az) =
      fun o => match o with
        | none => -c * az.1
        | some i => az.1 * blockDefectLinear c (x i) +
            blockDefectLinear c ((az.2 : QaryBlockRow K ι) i) := by
  sorry

/-- Exact injectivity of the literal building-up block generator. -/
theorem buildingUpBlockGenerator_injective
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (x : QaryBlockRow K ι) (ell : Module.Dual K C) (hc0 : c ≠ 0) :
    Function.Injective (buildingUpBlockGenerator (K := K) c C x ell) := by
  sorry

/-- The genuine building-up code preserves the isotropic intersection
dimension exactly. -/
theorem buildingUpBlockCode_inf_qaryIsotropicLineCode_finrank_exact
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (x : QaryBlockRow K ι) (ell : Module.Dual K C) (hc0 : c ≠ 0) :
    Module.finrank K
        ↥(buildingUpBlockCode (K := K) c C x ell ⊓
          qaryIsotropicLineCode (K := K) (ι := Option ι) c) =
      Module.finrank K
        ↥(C ⊓ qaryIsotropicLineCode (K := K) (ι := ι) c) := by
  sorry

/-- Exact finite-index rank-one induction step for the literal block form of
`buildRows`. -/
theorem finBuildingUpBlockCode_has_rankOne_orientedPairing_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (x : QaryBlockRow K (Fin n)) (ell : Module.Dual K C)
    (hc0 : c ≠ 0)
    (hone : Module.finrank K
      ↥(C ⊓ qaryIsotropicLineCode (K := K) c) = 1) :
    HasQaryRankOneOrientedPairing c
      (finBuildingUpBlockCode (K := K) c C x ell) := by
  sorry

/-- Exact equality between the scalar `buildRows` row space and its literal
block-code realization. -/
theorem prependedScalarRowSpace_buildRows_eq_buildingUpBlockCode_exact
    {m n : ℕ} (x : Fin (n * 2) → K) (c : K)
    (G : Matrix (Fin m) (Fin (n * 2)) K) :
    prependedScalarRowSpaceAsBlock (buildRows x c G) =
      buildingUpBlockCode (K := K) c (scalarRowSpaceAsBlock G)
        (finScalarBlockLinearEquiv (K := K) x)
        (blockDotFunctional x (scalarRowSpaceAsBlock G)) := by
  sorry

/-- Exact scalar/block row-space dictionary for the direct-sum branch. -/
theorem prependedScalarRowSpace_directSumRows_exact
    {m n : ℕ} (c : K) (G : Matrix (Fin m) (Fin (n * 2)) K) :
    prependedScalarRowSpaceAsBlock (directSumRows c G) =
      directSumBlockCode (K := K) (-c) (scalarRowSpaceAsBlock G) := by
  sorry

/-- Exact code equality induced by swapping the two new scalar coordinates. -/
theorem headSwap_directSumBlockCode_neg_exact
    (c : K) (C : Submodule K (QaryBlockRow K ι))
    (hc : c ^ 2 = (-1 : K)) :
    Submodule.map
        (scalarCoordinateReindexBlockLinearEquiv (K := K)
          (headBlockScalarSwap (ι := ι))).toLinearMap
        (directSumBlockCode (K := K) (-c) C) =
      directSumBlockCode (K := K) c C := by
  sorry

/-- Exact equality of the canonical and literal split direct-sum codes. -/
theorem canonicalSplitDirectSumCode_eq_directSumBlockCode_exact
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι)) :
    canonicalSplitDirectSumCode (K := K) c C =
      directSumBlockCode (K := K) c C := by
  sorry

/-- Exact finite-index conjugation of the new-block coordinate swap. -/
theorem finLastSwap_directSumBlockCode_neg_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (hc : c ^ 2 = (-1 : K)) :
    scalarCoordinatePermutedBlockCode (K := K)
        finLastBlockScalarSwap (finDirectSumBlockCode (K := K) (-c) C) =
      finDirectSumBlockCode (K := K) c C := by
  sorry

/-- Exact nonzero-coefficient elimination goal for the selected parent
defect column. -/
theorem parent_defect_relation_head_mem_span_exact
    [Fintype ι] (d : ι → V) (e : V) (coeff : Option ι → K)
    (hcoeff : coeff none ≠ 0)
    (hrel : ∑ j, coeff j • parentDefectFamily d e j = 0) :
    e ∈ span K (range d) := by
  sorry

/-- Exact corank-one selection goal for the parent defect family. -/
theorem exists_selected_defect_relation_of_corank_one_exact
    [Fintype ι] [DecidableEq ι] (f : ι → V)
    (hcorank : Module.finrank K (span K (range f)) + 1 = Fintype.card ι) :
    ∃ i : ι, ∃ coeff : Option {j : ι // j ≠ i} → K,
      coeff none ≠ 0 ∧
      (∑ o, coeff o •
        parentDefectFamily (fun j : {j : ι // j ≠ i} => f j) (f i) o = 0) ∧
      LinearIndependent K (fun j : {j : ι // j ≠ i} => f j) := by
  sorry

/-- Exact cross-pair merge goal used by the rank-one induction. -/
theorem paper_qary_rankOne_crossPair_merge_exact
    [Fintype ι] (c : K) (d : ι → V) (a b : V)
    (hc : c ≠ 0) (hd : LinearIndependent K d)
    (hdep : a + c • b ∈ span K (range d)) :
    Module.finrank K (span K (range (crossPairDefects c d a b))) =
      Fintype.card ι + 1 := by
  sorry

/-- Exact parent-defect relation form of the cross-pair merge goal. -/
theorem paper_qary_rankOne_crossPair_merge_of_parent_relation_exact
    [Fintype ι] (c : K) (d : ι → V) (a b : V)
    (coeff : Option ι → K)
    (hc : c ^ 2 = (-1 : K)) (hd : LinearIndependent K d)
    (hcoeff : coeff none ≠ 0)
    (hrel : ∑ j, coeff j •
      parentDefectFamily d (b - c • a) j = 0) :
    Module.finrank K (span K (range (crossPairDefects c d a b))) =
      Fintype.card ι + 1 := by
  sorry

/-- Literal identification of the cross-paired direct-sum defect family. -/
theorem crossPairedDirectSumDefects_eq_crossPairDefects
    (c : K) (d : ι → V) (a b : V) (hc : c ^ 2 = (-1 : K)) :
    crossPairedDirectSumDefects c d a b = crossPairDefects c d a b := by
  sorry

/-- Exact corank-one direct-sum branch at the defect-matrix level. -/
theorem exists_crossPaired_directSum_defect_rank_of_corank_one_exact
    [Fintype ι] [DecidableEq ι] (c : K) (a b : ι → V)
    (hc : c ^ 2 = (-1 : K))
    (hcorank : Module.finrank K
      (span K (range (fun i => b i - c • a i))) + 1 = Fintype.card ι) :
    ∃ i : ι,
      let d := fun j : {j : ι // j ≠ i} => b j - c • a j
      Module.finrank K
        (span K (range (crossPairedDirectSumDefects c d (a i) (b i)))) =
          Fintype.card {j : ι // j ≠ i} + 1 := by
  sorry

/-- Exact rank--nullity goal for a square finite column family. -/
theorem columnEvaluationDual_kernel_finrank_one_exact
    [Fintype ι] [FiniteDimensional K V] (v : ι → V)
    (hsquare : Module.finrank K V = Fintype.card ι)
    (hcorank : Module.finrank K (span K (range v)) + 1 = Fintype.card ι) :
    Module.finrank K
      (LinearMap.ker (columnEvaluationDual (K := K) v)) = 1 := by
  sorry

/-- Exact nullity-one direct-sum branch for the defect evaluation map. -/
theorem exists_crossPaired_directSum_defect_nullity_one_exact
    [Fintype ι] [DecidableEq ι] [FiniteDimensional K V]
    (c : K) (a b : ι → V)
    (hc : c ^ 2 = (-1 : K))
    (hsquare : Module.finrank K V = Fintype.card ι)
    (hcorank : Module.finrank K
      (span K (range (fun i => b i - c • a i))) + 1 = Fintype.card ι) :
    ∃ i : ι,
      let d := fun j : {j : ι // j ≠ i} => b j - c • a j
      Module.finrank K (LinearMap.ker
        (columnEvaluationDual (K := K)
          (crossPairedDirectSumDefects c d (a i) (b i)))) = 1 := by
  sorry

/-- Exact generated-code intersection goal, with row independence stated as
injectivity of the block-column generator. -/
theorem blockColumnGenerator_intersection_finrank_one_exact
    [Fintype ι] [FiniteDimensional K V]
    (c : K) (x y : ι → V)
    (hgen : Function.Injective (blockColumnGenerator (K := K) x y))
    (hsquare : Module.finrank K V = Fintype.card ι)
    (hcorank : Module.finrank K
      (span K (range (fun i => y i - c • x i))) + 1 = Fintype.card ι) :
    Module.finrank K
      ↥((LinearMap.range (blockColumnGenerator (K := K) x y) :
          Submodule K (QaryBlockRow K ι)) ⊓
        qaryIsotropicLineCode (K := K) c) = 1 := by
  sorry

/-- Exact identification of the literal child defect columns. -/
theorem crossPairedDirectSumColumns_defect_eq
    (c : K) (a b : ι → V) (i : ι) (hc : c ^ 2 = (-1 : K)) :
    (fun o => crossPairedDirectSumSecondColumns (K := K) a b i o -
      c • crossPairedDirectSumFirstColumns (K := K) c a i o) =
      crossPairedDirectSumDefects c
        (fun j : {j : ι // j ≠ i} => b j - c • a j) (a i) (b i) := by
  sorry

/-- Exact preservation of generator injectivity under cross-pairing. -/
theorem crossPairedDirectSum_blockColumnGenerator_injective
    (c : K) (a b : ι → V) (i : ι)
    (hparent : Function.Injective (blockColumnGenerator (K := K) a b)) :
    Function.Injective
      (blockColumnGenerator (K := K)
        (crossPairedDirectSumFirstColumns (K := K) c a i)
        (crossPairedDirectSumSecondColumns (K := K) a b i)) := by
  sorry

/-- Exact generated-code conclusion for the corank-one direct-sum branch. -/
theorem exists_crossPaired_directSum_code_intersection_finrank_one_exact
    [Fintype ι] [DecidableEq ι] [FiniteDimensional K V]
    (c : K) (a b : ι → V)
    (hc : c ^ 2 = (-1 : K))
    (hparent : Function.Injective (blockColumnGenerator (K := K) a b))
    (hsquare : Module.finrank K V = Fintype.card ι)
    (hcorank : Module.finrank K
      (span K (range (fun i => b i - c • a i))) + 1 = Fintype.card ι) :
    ∃ i : ι,
      let xChild := crossPairedDirectSumFirstColumns (K := K) c a i
      let yChild := crossPairedDirectSumSecondColumns (K := K) a b i
      Module.finrank K
        ↥((LinearMap.range (blockColumnGenerator (K := K) xChild yChild) :
            Submodule K (QaryBlockRow K (Option (Option {j : ι // j ≠ i})))) ⊓
          qaryIsotropicLineCode (K := K) c) = 1 := by
  sorry

/-- Exact canonical bidual realization of an arbitrary finite block code. -/
theorem canonicalBlockCodeGenerator_exact
    [Fintype ι] (C : Submodule K (QaryBlockRow K ι)) :
    Function.Injective (canonicalBlockCodeGenerator (K := K) C) ∧
      LinearMap.range (canonicalBlockCodeGenerator (K := K) C) = C := by
  sorry

/-- Exact defect-rank/intersection rank--nullity identity. -/
theorem blockColumnGenerator_defect_rank_add_intersection_finrank_exact
    [Fintype ι] [FiniteDimensional K V]
    (c : K) (x y : ι → V)
    (hgen : Function.Injective (blockColumnGenerator (K := K) x y)) :
    Module.finrank K (span K (range (fun i => y i - c • x i))) +
      Module.finrank K
        ↥((LinearMap.range (blockColumnGenerator (K := K) x y) :
            Submodule K (QaryBlockRow K ι)) ⊓
          qaryIsotropicLineCode (K := K) c) =
      Module.finrank K V := by
  sorry

/-- Exact conversion of canonical rank-one intersection to defect corank one. -/
theorem canonicalBlockCode_defect_corank_of_intersection_one_exact
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (hsquare : Module.finrank K C = Fintype.card ι)
    (hone : Module.finrank K
      ↥(C ⊓ qaryIsotropicLineCode (K := K) c) = 1) :
    Module.finrank K
      (span K (range (fun i =>
        blockCodeSecondCoordinate (K := K) C i -
          c • blockCodeFirstCoordinate (K := K) C i))) + 1 =
      Fintype.card ι := by
  sorry

/-- Exact rank-one preservation theorem for the canonical direct-sum branch. -/
theorem exists_crossPaired_canonicalCode_directSum_intersection_one_exact
    [Fintype ι] [DecidableEq ι]
    (c : K) (C : Submodule K (QaryBlockRow K ι))
    (hc : c ^ 2 = (-1 : K))
    (hsquare : Module.finrank K C = Fintype.card ι)
    (hone : Module.finrank K
      ↥(C ⊓ qaryIsotropicLineCode (K := K) c) = 1) :
    ∃ i : ι,
      let a := blockCodeFirstCoordinate (K := K) C
      let b := blockCodeSecondCoordinate (K := K) C
      let xChild := crossPairedDirectSumFirstColumns (K := K) c a i
      let yChild := crossPairedDirectSumSecondColumns (K := K) a b i
      Module.finrank K
        ↥((LinearMap.range (blockColumnGenerator (K := K) xChild yChild) :
            Submodule K (QaryBlockRow K (Option (Option {j : ι // j ≠ i})))) ⊓
          qaryIsotropicLineCode (K := K) c) = 1 := by
  sorry

/-- Exact scalar-coordinate reindexing identity for the child generator. -/
theorem crossPairedGenerator_eq_scalarCoordinateReindex_exact
    [DecidableEq ι] (c : K) (a b : ι → V) (i : ι) :
    blockColumnGenerator (K := K)
        (crossPairedDirectSumFirstColumns (K := K) c a i)
        (crossPairedDirectSumSecondColumns (K := K) a b i) =
      (scalarCoordinateReindexBlockLinearEquiv (K := K)
        (crossPairScalarEquiv i)).toLinearMap.comp
        (blockColumnGenerator (K := K)
          (splitDirectSumFirstColumns (K := K) a)
          (splitDirectSumSecondColumns (K := K) c b)) := by
  sorry

/-- Exact code-level scalar-coordinate permutation identity. -/
theorem crossPairedCode_eq_scalarCoordinateReindex_exact
    [DecidableEq ι] (c : K) (a b : ι → V) (i : ι) :
    LinearMap.range
        (blockColumnGenerator (K := K)
          (crossPairedDirectSumFirstColumns (K := K) c a i)
          (crossPairedDirectSumSecondColumns (K := K) a b i)) =
      Submodule.map
        (scalarCoordinateReindexBlockLinearEquiv (K := K)
          (crossPairScalarEquiv i)).toLinearMap
        (LinearMap.range
          (blockColumnGenerator (K := K)
            (splitDirectSumFirstColumns (K := K) a)
            (splitDirectSumSecondColumns (K := K) c b))) := by
  sorry

/-- Exact conjugation of the generic cross-pairing to `Fin (n+1) × Fin 2`. -/
theorem finCrossPair_scalarCoordinatePermuted_directSum_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (i : Fin n) :
    scalarCoordinatePermutedBlockCode (K := K)
        (finCrossPairScalarPerm i)
        (finCanonicalSplitDirectSumCode (K := K) c C) =
      relabelBlockCode (K := K)
        (finSuccEquivLast.trans
          (Equiv.optionCongr (Equiv.optionSubtypeNe i).symm))
        (LinearMap.range
          (blockColumnGenerator (K := K)
            (crossPairedDirectSumFirstColumns (K := K) c
              (blockCodeFirstCoordinate (K := K) C) i)
            (crossPairedDirectSumSecondColumns (K := K)
              (blockCodeFirstCoordinate (K := K) C)
              (blockCodeSecondCoordinate (K := K) C) i))) := by
  sorry

/-- Exact finite-index direct-sum rank-one induction step. -/
theorem finCanonicalSplitDirectSum_has_rankOne_orientedPairing_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (hc : c ^ 2 = (-1 : K))
    (hsquare : Module.finrank K C = n)
    (hone : Module.finrank K
      ↥(C ⊓ qaryIsotropicLineCode (K := K) c) = 1) :
    HasQaryRankOneOrientedPairing c
      (finCanonicalSplitDirectSumCode (K := K) c C) := by
  sorry

/-- Exact rank-one induction theorem for the literal `K(1,-c)` direct-sum
branch produced by `directSumRows`. -/
theorem finDirectSumBlockCode_neg_has_rankOne_orientedPairing_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (hc : c ^ 2 = (-1 : K))
    (hsquare : Module.finrank K C = n)
    (hone : Module.finrank K
      ↥(C ⊓ qaryIsotropicLineCode (K := K) c) = 1) :
    HasQaryRankOneOrientedPairing c
      (finDirectSumBlockCode (K := K) (-c) C) := by
  sorry

/-- Exact naturality of the literal direct sum under the parent permutation
extended while fixing the new block. -/
theorem optionHeadFixed_directSumBlockCode_exact
    {n : ℕ} (d : K) (σ : Equiv.Perm (Fin n × Fin 2))
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    Submodule.map
        (scalarCoordinateReindexBlockLinearEquiv (K := K)
          (optionHeadFixedScalarPerm σ).symm).toLinearMap
        (directSumBlockCode (K := K) d C) =
      directSumBlockCode (K := K) d
        (scalarCoordinatePermutedBlockCode (K := K) σ C) := by
  sorry

/-- Finite-index form of exact naturality for the literal direct sum. -/
theorem finExtendOld_directSumBlockCode_exact
    {n : ℕ} (d : K) (σ : Equiv.Perm (Fin n × Fin 2))
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    scalarCoordinatePermutedBlockCode (K := K) (finExtendOldScalarPerm σ)
        (finDirectSumBlockCode (K := K) d C) =
      finDirectSumBlockCode (K := K) d
        (scalarCoordinatePermutedBlockCode (K := K) σ C) := by
  sorry

/-- Permutation-free literal direct-sum induction step. -/
theorem finDirectSumBlockCode_neg_has_rankOne_orientedPairing_of_parent_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (hc : c ^ 2 = (-1 : K))
    (hsquare : Module.finrank K C = n)
    (hparent : HasQaryRankOneOrientedPairing c C) :
    HasQaryRankOneOrientedPairing c
      (finDirectSumBlockCode (K := K) (-c) C) := by
  sorry

/-- Exact transport of the literal building-up code, including its word and
dual functional, before finite reindexing. -/
theorem optionHeadFixed_buildingUpBlockCode_exact
    {n : ℕ} (c : K) (σ : Equiv.Perm (Fin n × Fin 2))
    (C : Submodule K (QaryBlockRow K (Fin n)))
    (x : QaryBlockRow K (Fin n)) (ell : Module.Dual K C) :
    let P := scalarCoordinatePermuteBlockLinearEquiv (K := K) σ
    let C' := scalarCoordinatePermutedBlockCode (K := K) σ C
    let E : C ≃ₗ[K] C' := P.submoduleMap C
    Submodule.map
        (scalarCoordinateReindexBlockLinearEquiv (K := K)
          (optionHeadFixedScalarPerm σ).symm).toLinearMap
        (buildingUpBlockCode (K := K) c C x ell) =
      buildingUpBlockCode (K := K) c C' (P x)
        (ell.comp E.symm.toLinearMap) := by
  sorry

/-- Finite-index naturality of the literal building-up code. -/
theorem finExtendOld_buildingUpBlockCode_exact
    {n : ℕ} (c : K) (σ : Equiv.Perm (Fin n × Fin 2))
    (C : Submodule K (QaryBlockRow K (Fin n)))
    (x : QaryBlockRow K (Fin n)) (ell : Module.Dual K C) :
    let P := scalarCoordinatePermuteBlockLinearEquiv (K := K) σ
    let C' := scalarCoordinatePermutedBlockCode (K := K) σ C
    let E : C ≃ₗ[K] C' := P.submoduleMap C
    scalarCoordinatePermutedBlockCode (K := K) (finExtendOldScalarPerm σ)
        (finBuildingUpBlockCode (K := K) c C x ell) =
      finBuildingUpBlockCode (K := K) c C' (P x)
        (ell.comp E.symm.toLinearMap) := by
  sorry

/-- Permutation-free literal building-up induction step. -/
theorem finBuildingUpBlockCode_has_rankOne_orientedPairing_of_parent_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (x : QaryBlockRow K (Fin n)) (ell : Module.Dual K C)
    (hc0 : c ≠ 0)
    (hparent : HasQaryRankOneOrientedPairing c C) :
    HasQaryRankOneOrientedPairing c
      (finBuildingUpBlockCode (K := K) c C x ell) := by
  sorry

/-- Literal decomposition of the product of isotropic lines. -/
theorem directSumBlockCode_qaryIsotropicLineCode_exact
    [Fintype ι] (c : K) :
    directSumBlockCode (K := K) c
        (qaryIsotropicLineCode (K := K) (ι := ι) c) =
      qaryIsotropicLineCode (K := K) (ι := Option ι) c := by
  sorry

/-- Finite-index form of the isotropic-line decomposition. -/
theorem finDirectSumBlockCode_qaryIsotropicLineCode_exact
    {n : ℕ} (c : K) :
    finDirectSumBlockCode (K := K) c
        (qaryIsotropicLineCode (K := K) (ι := Fin n) c) =
      qaryIsotropicLineCode (K := K) (ι := Fin (n + 1)) c := by
  sorry

/-- Rank-one oriented pairing for every nonempty terminal isotropic-line
code. -/
theorem qaryIsotropicLineCode_has_rankOne_orientedPairing_exact
    {n : ℕ} (hn : 0 < n) (c : K) (hc : c ^ 2 = (-1 : K)) :
    HasQaryRankOneOrientedPairing c
      (qaryIsotropicLineCode (K := K) (ι := Fin n) c) := by
  sorry

end BuildingUpFormalization.Components.QaryRankOnePairingMerge
