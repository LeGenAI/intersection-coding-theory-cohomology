import Formalization.Components.QaryRankBoxedNormalizationDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryRankOneOrientedPairing

open BuildingUpFormalization.Components.QaryRankBoxedNormalization

variable {K : Type*} [Field K]

/-- A scalar-coordinate permutation of a block-written ambient space.
Unlike `blockRelabelLinearEquiv`, this may separate the two entries of an old
block and therefore represents an arbitrary new oriented coordinate pairing. -/
def scalarCoordinatePermuteBlockLinearEquiv {n : ℕ}
    (σ : Equiv.Perm (Fin n × Fin 2)) :
    QaryBlockRow K (Fin n) ≃ₗ[K] QaryBlockRow K (Fin n) where
  toFun v i j :=
    v (σ.symm (i, j)).1 (σ.symm (i, j)).2
  invFun w i j :=
    w (σ (i, j)).1 (σ (i, j)).2
  left_inv v := by
    funext i j
    simp
  right_inv w := by
    funext i j
    simp
  map_add' u v := by rfl
  map_smul' a v := by rfl

/-- Transport a block-written code by an arbitrary scalar-coordinate
permutation, then read the target coordinates in their standard ordered
two-coordinate blocks. -/
def scalarCoordinatePermutedBlockCode {n : ℕ}
    (σ : Equiv.Perm (Fin n × Fin 2))
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    Submodule K (QaryBlockRow K (Fin n)) :=
  C.map (scalarCoordinatePermuteBlockLinearEquiv (K := K) σ).toLinearMap

/-- Exact universal rank-one target.  An arbitrary oriented pairing is
encoded by a scalar-coordinate permutation; rank one means that the permuted
code meets the standard product of isotropic lines in dimension exactly one. -/
def HasQaryRankOneOrientedPairing {n : ℕ} (c : K)
    (C : Submodule K (QaryBlockRow K (Fin n))) : Prop :=
  ∃ σ : Equiv.Perm (Fin n × Fin 2),
    Module.finrank K
      ↥(scalarCoordinatePermutedBlockCode (K := K) σ C ⊓
        qaryIsotropicLineCode (K := K) c) = 1

end BuildingUpFormalization.Components.QaryRankOneOrientedPairing
