import Formalization.Components.SplitBoxedDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.SplitBoxed

variable {K : Type*} [Field K]

@[simp] theorem blockDefect_isotropicLineBlock (c t : K) :
    blockDefect c (isotropicLineBlock c t) = 0 := by
  sorry

@[simp] theorem blockDefect_splitDiagonalBlock (c : K) :
    blockDefect c (splitDiagonalBlock (K := K)) = 1 := by
  sorry

@[simp] theorem blockDefectLinear_isotropicLineBlock (c t : K) :
    blockDefectLinear c (isotropicLineBlock c t) = 0 := by
  sorry

@[simp] theorem blockDefectLinear_splitDiagonalBlock (c : K) :
    blockDefectLinear c (splitDiagonalBlock (K := K)) = 1 := by
  sorry

theorem splitBoxedReadout_splitBoxedRows
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) (i : Option (Fin m)) :
    splitBoxedReadout c ell (splitBoxedRows c ell a b i) = Pi.single i 1 := by
  sorry

theorem splitBoxedRows_linearIndependent
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) :
    LinearIndependent K (splitBoxedRows c ell a b) := by
  sorry

theorem splitBlockRowInner_comm {m : ℕ} (R S : SplitBlockRow K m) :
    splitBlockRowInner R S = splitBlockRowInner S R := by
  sorry

theorem splitBlockRowBilin_isRefl {m : ℕ} :
    (splitBlockRowBilin (K := K) (m := m)).IsRefl := by
  sorry

theorem splitBlockRowBilin_separatingLeft {m : ℕ} :
    LinearMap.SeparatingLeft (splitBlockRowBilin (K := K) (m := m)) := by
  sorry

theorem splitBlockRowBilin_separatingRight {m : ℕ} :
    LinearMap.SeparatingRight (splitBlockRowBilin (K := K) (m := m)) := by
  sorry

theorem splitBlockRowBilin_nondegenerate {m : ℕ} :
    (splitBlockRowBilin (K := K) (m := m)).Nondegenerate := by
  sorry

theorem splitBoxedRows_rowSpace_finrank
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) :
    Module.finrank K ↥(splitBoxedRowSpace (splitBoxedRows c ell a b)) = m + 1 := by
  sorry

end BuildingUpFormalization.Components.SplitBoxed
