import Formalization.Components.RankBoxedConstruction

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryRankBoxedNormalization

open BuildingUpFormalization.Components.SplitBoxed
open BuildingUpFormalization.Components.RankBoxed

variable {K : Type*} [Field K]

/-- A vector written in two-coordinate blocks indexed by `ι`. -/
abbrev QaryBlockRow (K : Type*) (ι : Type*) := ι → SplitBlock K

/-- Euclidean inner product after grouping scalar coordinates into blocks. -/
def qaryBlockInner {ι : Type*} [Fintype ι]
    (R S : QaryBlockRow K ι) : K :=
  ∑ i, splitBlockInner (R i) (S i)

/-- Euclidean bilinear form in an arbitrary finite two-block indexing. -/
def qaryBlockBilin {ι : Type*} [Fintype ι] :
    LinearMap.BilinForm K (QaryBlockRow K ι) :=
  LinearMap.mk₂ K qaryBlockInner
    (by
      intro R S T
      simp [qaryBlockInner, splitBlockInner, dot_add_left,
        Finset.sum_add_distrib])
    (by
      intro a R S
      simp [qaryBlockInner, splitBlockInner, dot_smul_left,
        Finset.mul_sum])
    (by
      intro R S T
      simp [qaryBlockInner, splitBlockInner, dot_add_right,
        Finset.sum_add_distrib])
    (by
      intro a R S
      simp [qaryBlockInner, splitBlockInner, dot_smul_right,
        Finset.mul_sum])

/-- Self-duality for a code in two-coordinate block notation. -/
def QaryBlockSelfDualCode {ι : Type*} [Fintype ι]
    (C : Submodule K (QaryBlockRow K ι)) : Prop :=
  C = (qaryBlockBilin (K := K) (ι := ι)).orthogonal C

/-- The blockwise defect map
`(x,y) ↦ y - c*x`.  Its kernel is exactly the direct sum of the isotropic
lines `K(1,c)` used in the manuscript. -/
def qaryBlockDefectLinear {ι : Type*} (c : K) :
    QaryBlockRow K ι →ₗ[K] (ι → K) where
  toFun R i := blockDefectLinear c (R i)
  map_add' R S := by
    funext i
    simp
  map_smul' a R := by
    funext i
    simp

/-- The intrinsic subspace `U_c = ⨁_j K(1,c)`. -/
def qaryIsotropicLineCode {ι : Type*} (c : K) :
    Submodule K (QaryBlockRow K ι) :=
  LinearMap.ker (qaryBlockDefectLinear (K := K) (ι := ι) c)

/-- Reindex whole two-coordinate blocks.  This is a scalar-coordinate
permutation which moves each selected pair as a unit, not an arbitrary ambient
linear equivalence. -/
def blockRelabelLinearEquiv {ι κ : Type*} (σ : ι ≃ κ) :
    QaryBlockRow K κ ≃ₗ[K] QaryBlockRow K ι where
  toFun v i := v (σ i)
  invFun w j := w (σ.symm j)
  left_inv v := by funext j; simp
  right_inv w := by funext i; simp
  map_add' u v := rfl
  map_smul' a v := rfl

/-- Transport a block code along a block-coordinate permutation. -/
def relabelBlockCode {ι κ : Type*} (σ : ι ≃ κ)
    (C : Submodule K (QaryBlockRow K κ)) :
    Submodule K (QaryBlockRow K ι) :=
  Submodule.map (blockRelabelLinearEquiv (K := K) σ).toLinearMap C

/-- Exact universal rank-`r` boxed normal-form goal.

The lower-right `r × r` core is free but full rank.  The conclusion uses only
a permutation of whole two-coordinate blocks and equality of code submodules.
The two Gram relations are included explicitly. -/
def HasQaryRankBoxedNormalForm {n : ℕ} (c : K)
    (C : Submodule K (QaryBlockRow K (Fin n))) : Prop :=
  ∃ k r : ℕ,
    r = Module.finrank K ↥(C ⊓ qaryIsotropicLineCode (K := K) c) ∧
    k + r = n ∧
    ∃ (σ : RankBoxIndex k r ≃ Fin n)
      (P : Fin k → Fin k → K)
      (H Q : Fin k → Fin r → K)
      (A : Fin r → Fin k → K)
      (D : Fin r → Fin r → K),
      RankBoxCoreFullRank D ∧
      PivotMasterRelations Q A D ∧
      PivotGramRelations c P H Q ∧
      relabelBlockCode (K := K) σ C =
        rankBoxedRowSpace (rankBoxedRows c P H Q A D)

end BuildingUpFormalization.Components.QaryRankBoxedNormalization
