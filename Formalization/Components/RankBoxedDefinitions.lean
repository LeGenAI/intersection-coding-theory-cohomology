import Formalization.Components.SplitBoxedDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RankBoxed

open BuildingUpFormalization.Components.SplitBoxed

variable {K : Type*} [Field K]

/-- Row and block-column indices for a rank-`r` box: `k` pivot indices
followed by `r` master indices. -/
abbrev RankBoxIndex (k r : ℕ) := Sum (Fin k) (Fin r)

/-- A rank-boxed row written in two-coordinate blocks. -/
abbrev RankBoxRow (K : Type*) (k r : ℕ) :=
  RankBoxIndex k r → SplitBlock K

/-- The block `alpha * (1,c) + beta * (0,1)`.

Keeping both coefficients is essential.  The `alpha` coefficient on a pivot
diagonal cannot in general be normalized away in the rank-`r` q-ary boxed
form. -/
def splitAffineBlock (c alpha beta : K) : SplitBlock K :=
  head2 alpha (c * alpha + beta)

/-- The unnormalized rank-`r` boxed construction.

`P` is the free pivot-by-pivot isotropic coefficient matrix, `H` and `Q`
are the isotropic and transverse coefficients in the pivot-by-master corner,
`A` is the master-by-pivot coefficient matrix, and `D` is the free
master-by-master `r × r` core.  No identity normalization or rank hypothesis
is built into the data; invertibility of `D` belongs to the normal-form
theorem. -/
def rankBoxedRows {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K) :
    RankBoxIndex k r → RankBoxRow K k r
  | .inl i, .inl j =>
      splitAffineBlock c (P i j) (if i = j then 1 else 0)
  | .inl i, .inr t => splitAffineBlock c (H i t) (Q i t)
  | .inr s, .inl j => isotropicLineBlock c (A s j)
  | .inr s, .inr t => isotropicLineBlock c (D s t)

/-- Euclidean inner product of rank-boxed rows, split into the pivot and
master block columns.  Writing the two sums separately keeps the matrix
relations in the paper visible in the formal statement. -/
def rankBoxRowInner {k r : ℕ} (R S : RankBoxRow K k r) : K :=
  (∑ j : Fin k, splitBlockInner (R (.inl j)) (S (.inl j))) +
    ∑ t : Fin r, splitBlockInner (R (.inr t)) (S (.inr t))

/-- Pairwise Euclidean orthogonality of a rank-boxed row family. -/
def RankBoxedPairwiseOrthogonal {k r : ℕ}
    (R : RankBoxIndex k r → RankBoxRow K k r) : Prop :=
  ∀ i j, rankBoxRowInner (R i) (R j) = 0

/-- Row space of a rank-boxed family. -/
def rankBoxedRowSpace {k r : ℕ}
    (R : RankBoxIndex k r → RankBoxRow K k r) :
    Submodule K (RankBoxRow K k r) :=
  Submodule.span K (Set.range R)

/-- Euclidean bilinear form in rank-boxed block coordinates. -/
def rankBoxRowBilin {k r : ℕ} :
    LinearMap.BilinForm K (RankBoxRow K k r) :=
  LinearMap.mk₂ K rankBoxRowInner
    (by
      intro R S T
      simp [rankBoxRowInner, splitBlockInner, dot_add_left,
        Finset.sum_add_distrib]
      ring)
    (by
      intro a R S
      simp [rankBoxRowInner, splitBlockInner, dot_smul_left]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum])
    (by
      intro R S T
      simp [rankBoxRowInner, splitBlockInner, dot_add_right,
        Finset.sum_add_distrib]
      ring)
    (by
      intro a R S
      simp [rankBoxRowInner, splitBlockInner, dot_smul_right]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum])

/-- The lower-right `r × r` core has rank `r` precisely when its determinant
is nonzero.  Crucially, the construction does not set this core equal to the
identity matrix. -/
def RankBoxCoreFullRank {r : ℕ} (D : Fin r → Fin r → K) : Prop :=
  Matrix.det D ≠ 0

/-- The pivot--master orthogonality relation
`A + D Qᵀ = 0`, written entrywise in the row convention used by
`rankBoxedRows`. -/
def PivotMasterRelations {k r : ℕ}
    (Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K) : Prop :=
  ∀ s i, A s i + ∑ t, Q i t * D s t = 0

/-- The master-by-pivot coefficients forced by pivot--master
orthogonality.  They are not independent data. -/
def forcedMasterCoefficients {k r : ℕ}
    (Q : Fin k → Fin r → K)
    (D : Fin r → Fin r → K) : Fin r → Fin k → K :=
  fun s i => -(∑ t, Q i t * D s t)

/-- The rank-boxed rows with the forced master coefficients substituted. -/
def determinedRankBoxedRows {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (D : Fin r → Fin r → K) :
    RankBoxIndex k r → RankBoxRow K k r :=
  rankBoxedRows c P H Q (forcedMasterCoefficients Q D) D

/-- Euclidean inner product of two terminal block-rows. -/
def terminalRowInner {r : ℕ}
    (ell ell' : Fin r → SplitBlock K) : K :=
  ∑ t, splitBlockInner (ell t) (ell' t)

/-- Inner product of two indexed terminal rows in the paper form. -/
def terminalInner {k r : ℕ}
    (ell : Fin k → Fin r → SplitBlock K) (i j : Fin k) : K :=
  terminalRowInner (ell i) (ell j)

/-- First coordinates of the terminal blocks. -/
def terminalFirst {k r : ℕ}
    (ell : Fin k → Fin r → SplitBlock K) : Fin k → Fin r → K :=
  fun i t => ell i t 0

/-- Transverse coordinates of the terminal blocks. -/
def terminalDefect {k r : ℕ} (c : K)
    (ell : Fin k → Fin r → SplitBlock K) : Fin k → Fin r → K :=
  fun i t => blockDefectLinear c (ell i t)

/-- The pivot diagonal forced by self-orthogonality in odd characteristic. -/
def forcedPivotDiagonal {k r : ℕ} (c : K)
    (ell : Fin k → Fin r → SplitBlock K) (i : Fin k) : K :=
  c / 2 * (1 + terminalInner ell i i)

/-- Pivot coefficients in the minimal paper parametrization.  Only the
off-diagonal values of `b` are used; the diagonal is forced by `ell`. -/
def paperPivotCoefficients {k r : ℕ} (c : K)
    (b : Fin k → Fin k → K)
    (ell : Fin k → Fin r → SplitBlock K) : Fin k → Fin k → K :=
  fun i j => if i = j then forcedPivotDiagonal c ell i else b i j

/-- The universal rank-boxed rows in the paper parametrization
`G(c;b,ell,D)`. -/
def paperRankBoxedRows {k r : ℕ} (c : K)
    (b : Fin k → Fin k → K)
    (ell : Fin k → Fin r → SplitBlock K)
    (D : Fin r → Fin r → K) :
    RankBoxIndex k r → RankBoxRow K k r :=
  determinedRankBoxedRows c (paperPivotCoefficients c b ell)
    (terminalFirst ell) (terminalDefect c ell) D

/-- The sole Gram condition in the minimal paper parametrization. -/
def PaperOffDiagonalRelations {k r : ℕ} (c : K)
    (b : Fin k → Fin k → K)
    (ell : Fin k → Fin r → SplitBlock K) : Prop :=
  ∀ i j, i ≠ j → c * (b i j + b j i) + terminalInner ell i j = 0

/-- The pivot--pivot Gram relation.  Under `c² = -1` it is exactly

`I + c(P + Pᵀ) + c(HQᵀ + QHᵀ) + QQᵀ = 0`.

The diagonal of `P` is retained because it cannot be normalized away over a
general q-ary field. -/
def PivotGramRelations {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K) : Prop :=
  ∀ i j,
    (if i = j then 1 else 0) + c * (P i j + P j i) +
      ∑ t, (c * (H i t * Q j t + Q i t * H j t) + Q i t * Q j t) = 0

/-- Block-triangular readout for the rank-boxed family.  Pivot outputs use
the transverse functional `blockDefect`; master outputs subtract the known
`H` contribution from the first coordinate. -/
def rankBoxedReadout {k r : ℕ}
    (c : K) (H : Fin k → Fin r → K) :
    RankBoxRow K k r →ₗ[K] (RankBoxIndex k r → K) where
  toFun R
    | .inl j => blockDefectLinear c (R (.inl j))
    | .inr t =>
        R (.inr t) 0 -
          ∑ i, H i t * blockDefectLinear c (R (.inl i))
  map_add' R S := by
    funext x
    cases x with
    | inl j => simp
    | inr t =>
        simp [mul_add, Finset.sum_add_distrib]
        ring
  map_smul' a R := by
    funext x
    cases x with
    | inl j => simp
    | inr t =>
        simp [mul_left_comm]
        rw [mul_sub, Finset.mul_sum]

/-- The block-diagonal family obtained by applying `rankBoxedReadout` to
`rankBoxedRows`: an identity pivot block and the free core `D`. -/
def rankBoxedReadoutRows {k r : ℕ}
    (D : Fin r → Fin r → K) :
    RankBoxIndex k r → (RankBoxIndex k r → K)
  | .inl i, .inl j => if i = j then 1 else 0
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0
  | .inr s, .inr t => D s t

/-- Rank-one characteristic-two specialization of `rankBoxedRows`.

The four constant-one corners are chosen so that, in characteristic two,
the terminal pivot block is `(1,0)`, every master block is `(1,1)`, and the
pivot diagonal is `(0,1)` when `b i i = 0`.  Thus this is the literal
Chinburg--Zhang block pattern used in Theorem 3.4. -/
def binaryCzRankOneRows {k : ℕ} (b : Fin k → Fin k → K) :
    RankBoxIndex k 1 → RankBoxRow K k 1 :=
  rankBoxedRows 1 b
    (fun _ _ => 1) (fun _ _ => 1)
    (fun _ _ => 1) (fun _ _ => 1)

end BuildingUpFormalization.Components.RankBoxed
