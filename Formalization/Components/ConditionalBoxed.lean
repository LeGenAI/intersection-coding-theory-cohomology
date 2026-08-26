import Formalization.Components.SplitBoxedOrthogonality

set_option autoImplicit false

namespace BuildingUpFormalization.Components.SplitBoxed

variable {K : Type*} [Field K]

/-- Exact coefficient theorem for the displayed adapted generator matrix.
All block-shape assumptions are explicit. The form is Euclidean throughout. -/
theorem paper_conditional_boxed_normalization_exact
    {m : ℕ} (c : K) (hc : c ^ 2 = (-1 : K))
    (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K)
    (R : Option (Fin m) → SplitBlockRow K m)
    (C : Submodule K (SplitBlockRow K m))
    (hC : C = (splitBlockRowBilin (K := K) (m := m)).orthogonal C)
    (hgen : splitBoxedRowSpace R = C)
    (hfinal : R none none = isotropicLineBlock c 1)
    (hfinalLeft : ∀ j, R none (some j) = isotropicLineBlock c (a j))
    (hlast : ∀ i, R (some i) none = ell i)
    (hdiag : ∀ i, R (some i) (some i) = splitDiagonalBlock)
    (hother : ∀ i j, i ≠ j →
      R (some i) (some j) = isotropicLineBlock c (b i j)) :
    R = splitBoxedRows c ell a b ∧
      (∀ i, dot (ell i) (ell i) = (-1 : K)) ∧
      (∀ i, ell i 0 + c * ell i 1 = -c * a i) ∧
      (∀ i j, i < j → c * (b i j + b j i) + dot (ell i) (ell j) = 0) ∧
      C = splitBoxedRowSpace (splitBoxedRows c ell a b) := by
  have hR : R = splitBoxedRows c ell a b := by
    funext i j
    cases i with
    | none =>
        cases j with
        | none => exact hfinal
        | some j => exact hfinalLeft j
    | some i =>
        cases j with
        | none => exact hlast i
        | some j =>
            by_cases hij : i = j
            · subst j; simpa [splitBoxedRows] using hdiag i
            · simpa [splitBoxedRows, hij] using hother i j hij
  have hmem (i) : R i ∈ C := by
    rw [← hgen]
    exact Submodule.subset_span (Set.mem_range_self i)
  have horth (i j) : splitBlockRowInner
      (splitBoxedRows c ell a b i) (splitBoxedRows c ell a b j) = 0 := by
    have hj : R j ∈ (splitBlockRowBilin (K := K) (m := m)).orthogonal C :=
      hC ▸ hmem j
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hj) (R i) (hmem i)
    simpa [LinearMap.BilinForm.isOrtho_def, hR] using h
  refine ⟨hR, ?_, ?_, ?_, ?_⟩
  · intro i
    have h := horth (some i) (some i)
    rw [splitBoxedRows_nonfinal_self c ell a b hc i] at h
    linear_combination h
  · intro i
    have h := horth (some i) none
    rw [splitBoxedRows_nonfinal_final_inner c ell a b hc i] at h
    linear_combination h
  · intro i j hij
    simpa [splitBoxedRows_nonfinal_inner c ell a b hc (ne_of_lt hij)] using
      horth (some i) (some j)
  · rw [← hR, hgen]

end BuildingUpFormalization.Components.SplitBoxed
