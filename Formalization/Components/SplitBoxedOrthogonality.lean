import Formalization.Components.SplitBoxed

set_option autoImplicit false

namespace BuildingUpFormalization.Components.SplitBoxed

variable {K : Type*} [Field K]

theorem splitBlockInner_isotropicLine_isotropicLine
    (c s t : K) (hc : c ^ 2 = (-1 : K)) :
    splitBlockInner (isotropicLineBlock c s) (isotropicLineBlock c t) = 0 := by
  simp [splitBlockInner, isotropicLineBlock, dot, head2]
  rw [show c * s * (c * t) = c ^ 2 * (s * t) by ring, hc]
  ring

theorem splitBlockInner_diagonal_isotropicLine (c t : K) :
    splitBlockInner (splitDiagonalBlock (K := K)) (isotropicLineBlock c t) = c * t := by
  simp [splitBlockInner, splitDiagonalBlock, isotropicLineBlock, dot, head2]

theorem splitBlockInner_isotropicLine_diagonal (c t : K) :
    splitBlockInner (isotropicLineBlock c t) (splitDiagonalBlock (K := K)) = c * t := by
  simp [splitBlockInner, splitDiagonalBlock, isotropicLineBlock, dot, head2]

/-- The two off-diagonal blocks contribute exactly
`c*b_ji + c*b_ij = c*(b_ij+b_ji)`. -/
theorem splitBoxed_offDiagonal_two_block_contribution
    (c b_ij b_ji : K) :
    splitBlockInner (splitDiagonalBlock (K := K)) (isotropicLineBlock c b_ji) +
        splitBlockInner (isotropicLineBlock c b_ij) (splitDiagonalBlock (K := K)) =
      c * (b_ij + b_ji) := by
  rw [splitBlockInner_diagonal_isotropicLine,
    splitBlockInner_isotropicLine_diagonal]
  ring

/-- Exact inner-product expansion for two distinct non-final boxed rows. -/
theorem splitBoxedRows_nonfinal_inner
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) (hc : c ^ 2 = (-1 : K))
    {i j : Fin m} (hij : i ≠ j) :
    splitBlockRowInner (splitBoxedRows c ell a b (some i))
        (splitBoxedRows c ell a b (some j)) =
      c * (b i j + b j i) + dot (ell i) (ell j) := by
  classical
  rw [splitBlockRowInner, Fintype.sum_option]
  have hterm (k : Fin m) :
      splitBlockInner (splitBoxedRows c ell a b (some i) (some k))
          (splitBoxedRows c ell a b (some j) (some k)) =
        if k = i then c * b j i else if k = j then c * b i j else 0 := by
    by_cases hki : k = i
    · subst k
      simp only [splitBoxedRows, if_pos, if_neg (Ne.symm hij)]
      exact splitBlockInner_diagonal_isotropicLine c (b j i)
    · by_cases hkj : k = j
      · subst k
        simp only [splitBoxedRows, if_neg hij, if_pos, if_neg (Ne.symm hij)]
        exact splitBlockInner_isotropicLine_diagonal c (b i j)
      · simp only [splitBoxedRows, if_neg (Ne.symm hki),
          if_neg (Ne.symm hkj), hki, hkj]
        exact splitBlockInner_isotropicLine_isotropicLine c _ _ hc
  simp_rw [hterm]
  have hsplit (k : Fin m) :
      (if k = i then c * b j i else if k = j then c * b i j else 0) =
        (if k = i then c * b j i else 0) +
          (if k = j then c * b i j else 0) := by
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [hki, hkj, hij, Ne.symm hij]
  simp_rw [hsplit, Finset.sum_add_distrib]
  simp [splitBoxedRows, splitBlockInner]
  ring

/-- Self-inner-product of a non-final boxed row. -/
theorem splitBoxedRows_nonfinal_self
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) (hc : c ^ 2 = (-1 : K)) (i : Fin m) :
    splitBlockRowInner (splitBoxedRows c ell a b (some i))
        (splitBoxedRows c ell a b (some i)) =
      1 + dot (ell i) (ell i) := by
  classical
  rw [splitBlockRowInner, Fintype.sum_option]
  have hterm (k : Fin m) :
      splitBlockInner (splitBoxedRows c ell a b (some i) (some k))
          (splitBoxedRows c ell a b (some i) (some k)) =
        if i = k then 1 else 0 := by
    by_cases hik : i = k
    · subst k
      simp [splitBoxedRows, splitBlockInner, splitDiagonalBlock, dot, head2]
    · simp [splitBoxedRows, hik,
        splitBlockInner_isotropicLine_isotropicLine, hc]
  simp_rw [hterm]
  simp [splitBoxedRows, splitBlockInner]
  ring

/-- The final boxed row is isotropic. -/
theorem splitBoxedRows_final_self
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) (hc : c ^ 2 = (-1 : K)) :
    splitBlockRowInner (splitBoxedRows c ell a b none)
        (splitBoxedRows c ell a b none) = 0 := by
  classical
  rw [splitBlockRowInner, Fintype.sum_option]
  simp [splitBoxedRows, splitBlockInner_isotropicLine_isotropicLine, hc]

/-- Exact inner-product expansion between a non-final row and the final row. -/
theorem splitBoxedRows_nonfinal_final_inner
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) (hc : c ^ 2 = (-1 : K)) (i : Fin m) :
    splitBlockRowInner (splitBoxedRows c ell a b (some i))
        (splitBoxedRows c ell a b none) =
      c * a i + (ell i 0 + c * ell i 1) := by
  classical
  rw [splitBlockRowInner, Fintype.sum_option]
  have hterm (k : Fin m) :
      splitBlockInner (splitBoxedRows c ell a b (some i) (some k))
          (splitBoxedRows c ell a b none (some k)) =
        if i = k then c * a i else 0 := by
    by_cases hik : i = k
    · subst k
      simpa [splitBoxedRows] using
        splitBlockInner_diagonal_isotropicLine c (a i)
    · simp [splitBoxedRows, hik,
        splitBlockInner_isotropicLine_isotropicLine, hc]
  simp_rw [hterm]
  simp [splitBoxedRows, splitBlockInner, isotropicLineBlock, head2, dot]
  ring

/-- The three coefficient conditions in Theorem 3.12 imply orthogonality of
all displayed boxed rows. -/
theorem splitBoxedRows_pairwiseOrthogonal
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K)
    (hc : c ^ 2 = (-1 : K))
    (hnorm : ∀ i, dot (ell i) (ell i) = (-1 : K))
    (hlast : ∀ i, ell i 0 + c * ell i 1 = -c * a i)
    (hoff : ∀ i j, i < j →
      c * (b i j + b j i) + dot (ell i) (ell j) = 0) :
    SplitBoxedPairwiseOrthogonal (splitBoxedRows c ell a b) := by
  intro i j
  cases i with
  | none =>
      cases j with
      | none => exact splitBoxedRows_final_self c ell a b hc
      | some j =>
          rw [splitBlockRowInner_comm,
            splitBoxedRows_nonfinal_final_inner c ell a b hc j, hlast]
          ring
  | some i =>
      cases j with
      | none =>
          rw [splitBoxedRows_nonfinal_final_inner c ell a b hc i, hlast]
          ring
      | some j =>
          by_cases hij : i = j
          · subst j
            rw [splitBoxedRows_nonfinal_self c ell a b hc i, hnorm]
            ring
          · rw [splitBoxedRows_nonfinal_inner c ell a b hc hij]
            rcases lt_or_gt_of_ne hij with hijlt | hjilt
            · exact hoff i j hijlt
            · calc
                c * (b i j + b j i) + dot (ell i) (ell j) =
                    c * (b j i + b i j) + dot (ell j) (ell i) := by
                      rw [dot_comm]
                      ring
                _ = 0 := hoff j i hjilt

theorem splitBoxedRowSpace_le_orthogonal
    {m : ℕ} {R : Option (Fin m) → SplitBlockRow K m}
    (hR : SplitBoxedPairwiseOrthogonal R) :
    splitBoxedRowSpace R ≤
      (splitBlockRowBilin (K := K) (m := m)).orthogonal
        (splitBoxedRowSpace R) := by
  rw [splitBoxedRowSpace]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  apply (LinearMap.BilinForm.mem_orthogonal_iff).2
  intro w hw
  refine Submodule.span_induction
    (p := fun z _ =>
      (splitBlockRowBilin (K := K) (m := m)).IsOrtho z (R i))
    ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨j, rfl⟩
    rw [LinearMap.BilinForm.isOrtho_def, splitBlockRowBilin_apply]
    exact hR j i
  · simpa using
      (LinearMap.BilinForm.isOrtho_zero_left
        (B := splitBlockRowBilin (K := K) (m := m)) (x := R i))
  · intro x y hx hy hx0 hy0
    rw [LinearMap.BilinForm.isOrtho_def] at hx0 hy0 ⊢
    simp [hx0, hy0]
  · intro t x hx hx0
    rw [LinearMap.BilinForm.isOrtho_def] at hx0 ⊢
    simp [hx0]

/-- Self-duality of the exact boxed row space in its `2(m+1)` split
coordinates. -/
theorem splitBoxedRows_rowSpace_selfDual
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K)
    (horth : SplitBoxedPairwiseOrthogonal (splitBoxedRows c ell a b)) :
    splitBoxedRowSpace (splitBoxedRows c ell a b) =
      (splitBlockRowBilin (K := K) (m := m)).orthogonal
        (splitBoxedRowSpace (splitBoxedRows c ell a b)) := by
  let C := splitBoxedRowSpace (splitBoxedRows c ell a b)
  let B := splitBlockRowBilin (K := K) (m := m)
  have hle : C ≤ B.orthogonal C := by
    exact splitBoxedRowSpace_le_orthogonal horth
  have hadd :
      Module.finrank K ↥C + Module.finrank K ↥(B.orthogonal C) =
        Module.finrank K (SplitBlockRow K m) +
          Module.finrank K ↥(C ⊓ B.orthogonal ⊤) := by
    simpa [B, C] using
      (LinearMap.BilinForm.finrank_add_finrank_orthogonal
        (B := B) (splitBlockRowBilin_isRefl (K := K) (m := m)) C)
  have htop : B.orthogonal ⊤ = ⊥ := by
    rw [LinearMap.BilinForm.orthogonal_top_eq_ker
      (B := B) (splitBlockRowBilin_isRefl (K := K) (m := m))]
    exact (splitBlockRowBilin_nondegenerate (K := K) (m := m)).ker_eq_bot
  have hambient : Module.finrank K (SplitBlockRow K m) = 2 * (m + 1) := by
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_fintype_fun_eq_card]
    omega
  have hdim : Module.finrank K ↥C = m + 1 := by
    exact splitBoxedRows_rowSpace_finrank c ell a b
  have hfinOrth : Module.finrank K ↥(B.orthogonal C) = m + 1 := by
    have hcalc := hadd
    rw [htop, inf_bot_eq] at hcalc
    simp [hambient] at hcalc
    omega
  apply Submodule.eq_of_le_of_finrank_eq hle
  exact hdim.trans hfinOrth.symm

/-- Exact paper-facing formalization of Theorem 3.12. -/
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
  have horth := splitBoxedRows_pairwiseOrthogonal c ell a b hc hnorm hlast hoff
  exact ⟨horth, splitBoxedRows_linearIndependent c ell a b,
    splitBoxedRows_rowSpace_selfDual c ell a b horth⟩

end BuildingUpFormalization.Components.SplitBoxed
