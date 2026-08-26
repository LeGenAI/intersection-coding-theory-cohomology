import Formalization.Archive.SubmittedBaseline

set_option autoImplicit false

namespace BuildingUpFormalization.Components.SplitBoxed

variable {K : Type*} [Field K]

/-- A two-coordinate block in the split boxed presentation. -/
abbrev SplitBlock (K : Type*) := Fin 2 → K

/-- A row with `m` non-final blocks and one distinguished final block. -/
abbrev SplitBlockRow (K : Type*) (m : ℕ) := Option (Fin m) → SplitBlock K

/-- The isotropic-line block `t(1,c)`. -/
def isotropicLineBlock (c t : K) : SplitBlock K := head2 t (c * t)

/-- The distinguished non-final diagonal block `(0,1)`. -/
def splitDiagonalBlock : SplitBlock K := head2 0 1

/-- The paper's split boxed row family. `none` is the final row/block and
`some i` is the `i`th non-final row/block. -/
def splitBoxedRows {m : ℕ}
    (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) :
    Option (Fin m) → SplitBlockRow K m
  | none, none => isotropicLineBlock c 1
  | none, some j => isotropicLineBlock c (a j)
  | some i, none => ell i
  | some i, some j =>
      if i = j then splitDiagonalBlock else isotropicLineBlock c (b i j)

/-- Euclidean inner product of two two-coordinate blocks. -/
def splitBlockInner (u v : SplitBlock K) : K := dot u v

/-- Euclidean inner product of block rows, summed over all block columns. -/
def splitBlockRowInner {m : ℕ} (R S : SplitBlockRow K m) : K :=
  ∑ j, splitBlockInner (R j) (S j)

/-- Pairwise Euclidean orthogonality for a family of split block rows. -/
def SplitBoxedPairwiseOrthogonal {m : ℕ}
    (R : Option (Fin m) → SplitBlockRow K m) : Prop :=
  ∀ i j, splitBlockRowInner (R i) (R j) = 0

/-- Row space of a family written in split block coordinates. -/
def splitBoxedRowSpace {m : ℕ}
    (R : Option (Fin m) → SplitBlockRow K m) : Submodule K (SplitBlockRow K m) :=
  Submodule.span K (Set.range R)

/-- Euclidean bilinear form in split block coordinates. -/
def splitBlockRowBilin {m : ℕ} : LinearMap.BilinForm K (SplitBlockRow K m) :=
  LinearMap.mk₂ K splitBlockRowInner
    (by
      intro R S T
      simp [splitBlockRowInner, splitBlockInner, dot_add_left,
        Finset.sum_add_distrib])
    (by
      intro t R S
      simp [splitBlockRowInner, splitBlockInner, dot_smul_left]
      rw [mul_add, Finset.mul_sum])
    (by
      intro R S T
      simp [splitBlockRowInner, splitBlockInner, dot_add_right,
        Finset.sum_add_distrib])
    (by
      intro t R S
      simp [splitBlockRowInner, splitBlockInner, dot_smul_right]
      rw [mul_add, Finset.mul_sum])

@[simp] theorem splitBlockRowBilin_apply {m : ℕ} (R S : SplitBlockRow K m) :
    splitBlockRowBilin R S = splitBlockRowInner R S := by
  rfl

/-- The functional `f(s,t)=t-cs`, which vanishes on `K(1,c)` and is one on
the distinguished diagonal block `(0,1)`. -/
def blockDefect (c : K) (v : SplitBlock K) : K := v 1 - c * v 0

def blockDefectLinear (c : K) : SplitBlock K →ₗ[K] K where
  toFun := blockDefect c
  map_add' u v := by
    simp [blockDefect]
    ring
  map_smul' t v := by
    simp [blockDefect]
    ring

/-- A linear readout for boxed rows. The non-final outputs apply
`blockDefect`; the final output subtracts the predictable `ell` contribution.
It sends every boxed row to the corresponding standard basis vector. -/
def splitBoxedReadout {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) :
    SplitBlockRow K m →ₗ[K] (Option (Fin m) → K) where
  toFun R
    | some j => blockDefectLinear c (R (some j))
    | none => R none 0 - ∑ j, ell j 0 * blockDefectLinear c (R (some j))
  map_add' R S := by
    funext j
    cases j with
    | some j => simp
    | none =>
        simp [mul_add, Finset.sum_add_distrib]
        ring
  map_smul' t R := by
    funext j
    cases j with
    | some j => simp
    | none =>
        simp [mul_left_comm]
        rw [mul_sub, Finset.mul_sum]

end BuildingUpFormalization.Components.SplitBoxed
