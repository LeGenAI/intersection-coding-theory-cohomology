import Formalization.Components.SplitBoxedDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.SplitBoxed

variable {K : Type*} [Field K]

theorem splitBlockInner_isotropicLine_isotropicLine
    (c s t : K) (hc : c ^ 2 = (-1 : K)) :
    splitBlockInner (isotropicLineBlock c s) (isotropicLineBlock c t) = 0 := by
  sorry

theorem splitBlockInner_diagonal_isotropicLine (c t : K) :
    splitBlockInner (splitDiagonalBlock (K := K)) (isotropicLineBlock c t) = c * t := by
  sorry

theorem splitBlockInner_isotropicLine_diagonal (c t : K) :
    splitBlockInner (isotropicLineBlock c t) (splitDiagonalBlock (K := K)) = c * t := by
  sorry

theorem splitBoxed_offDiagonal_two_block_contribution
    (c b_ij b_ji : K) :
    splitBlockInner (splitDiagonalBlock (K := K)) (isotropicLineBlock c b_ji) +
        splitBlockInner (isotropicLineBlock c b_ij) (splitDiagonalBlock (K := K)) =
      c * (b_ij + b_ji) := by
  sorry

theorem splitBoxedRows_nonfinal_inner
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) (hc : c ^ 2 = (-1 : K))
    {i j : Fin m} (hij : i ≠ j) :
    splitBlockRowInner (splitBoxedRows c ell a b (some i))
        (splitBoxedRows c ell a b (some j)) =
      c * (b i j + b j i) + dot (ell i) (ell j) := by
  sorry

theorem splitBoxedRows_nonfinal_self
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) (hc : c ^ 2 = (-1 : K)) (i : Fin m) :
    splitBlockRowInner (splitBoxedRows c ell a b (some i))
        (splitBoxedRows c ell a b (some i)) =
      1 + dot (ell i) (ell i) := by
  sorry

theorem splitBoxedRows_final_self
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) (hc : c ^ 2 = (-1 : K)) :
    splitBlockRowInner (splitBoxedRows c ell a b none)
        (splitBoxedRows c ell a b none) = 0 := by
  sorry

theorem splitBoxedRows_nonfinal_final_inner
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) (hc : c ^ 2 = (-1 : K)) (i : Fin m) :
    splitBlockRowInner (splitBoxedRows c ell a b (some i))
        (splitBoxedRows c ell a b none) =
      c * a i + (ell i 0 + c * ell i 1) := by
  sorry

theorem splitBoxedRows_pairwiseOrthogonal
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K)
    (hc : c ^ 2 = (-1 : K))
    (hnorm : ∀ i, dot (ell i) (ell i) = (-1 : K))
    (hlast : ∀ i, ell i 0 + c * ell i 1 = -c * a i)
    (hoff : ∀ i j, i < j →
      c * (b i j + b j i) + dot (ell i) (ell j) = 0) :
    SplitBoxedPairwiseOrthogonal (splitBoxedRows c ell a b) := by
  sorry

theorem splitBoxedRowSpace_le_orthogonal
    {m : ℕ} {R : Option (Fin m) → SplitBlockRow K m}
    (hR : SplitBoxedPairwiseOrthogonal R) :
    splitBoxedRowSpace R ≤
      (splitBlockRowBilin (K := K) (m := m)).orthogonal
        (splitBoxedRowSpace R) := by
  sorry

theorem splitBoxedRows_rowSpace_selfDual
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K)
    (horth : SplitBoxedPairwiseOrthogonal (splitBoxedRows c ell a b)) :
    splitBoxedRowSpace (splitBoxedRows c ell a b) =
      (splitBlockRowBilin (K := K) (m := m)).orthogonal
        (splitBoxedRowSpace (splitBoxedRows c ell a b)) := by
  sorry

theorem paper_split_boxed_form_exact
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K)
    (hc : c ^ 2 = (-1 : K))
    (hnorm : ∀ i, dot (ell i) (ell i) = (-1 : K))
    (hlast : ∀ i, ell i 0 + c * ell i 1 = -c * a i)
    (hoff : ∀ i j, i < j →
      c * (b i j + b j i) + dot (ell i) (ell j) = 0) :
    SplitBoxedPairwiseOrthogonal (splitBoxedRows c ell a b) ∧
      LinearIndependent K (splitBoxedRows c ell a b) ∧
      splitBoxedRowSpace (splitBoxedRows c ell a b) =
        (splitBlockRowBilin (K := K) (m := m)).orthogonal
          (splitBoxedRowSpace (splitBoxedRows c ell a b)) := by
  sorry

end BuildingUpFormalization.Components.SplitBoxed
