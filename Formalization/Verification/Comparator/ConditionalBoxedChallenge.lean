import Formalization.Components.SplitBoxedDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.SplitBoxed

variable {K : Type*} [Field K]

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
  sorry

end BuildingUpFormalization.Components.SplitBoxed

