import Formalization.Components.SplitBoxedDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.SplitBoxed

variable {K : Type*} [Field K]

@[simp] theorem blockDefect_isotropicLineBlock (c t : K) :
    blockDefect c (isotropicLineBlock c t) = 0 := by
  simp [blockDefect, isotropicLineBlock, head2]

@[simp] theorem blockDefect_splitDiagonalBlock (c : K) :
    blockDefect c (splitDiagonalBlock (K := K)) = 1 := by
  simp [blockDefect, splitDiagonalBlock, head2]

@[simp] theorem blockDefectLinear_isotropicLineBlock (c t : K) :
    blockDefectLinear c (isotropicLineBlock c t) = 0 := by
  exact blockDefect_isotropicLineBlock c t

@[simp] theorem blockDefectLinear_splitDiagonalBlock (c : K) :
    blockDefectLinear c (splitDiagonalBlock (K := K)) = 1 := by
  exact blockDefect_splitDiagonalBlock c

/-- The boxed readout sends each displayed row to the matching standard basis
vector. This is the functional proof replacing the paper's elimination claim. -/
theorem splitBoxedReadout_splitBoxedRows
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) (i : Option (Fin m)) :
    splitBoxedReadout c ell (splitBoxedRows c ell a b i) = Pi.single i 1 := by
  classical
  funext j
  cases i with
  | none =>
      cases j with
      | none => simp [splitBoxedReadout, splitBoxedRows, blockDefectLinear,
          blockDefect, isotropicLineBlock, head2]
      | some j => simp [splitBoxedReadout, splitBoxedRows, blockDefectLinear]
  | some i =>
      cases j with
      | none =>
          change ell i 0 - ∑ x, ell x 0 *
            blockDefect c
              (if i = x then splitDiagonalBlock else isotropicLineBlock c (b i x)) = 0
          rw [Finset.sum_eq_single i]
          · simp [blockDefect, splitDiagonalBlock, head2]
          · intro x _ hxi
            simp [Ne.symm hxi]
          · simp
      | some j =>
          by_cases hij : i = j
          · subst j
            simp [splitBoxedReadout, splitBoxedRows, blockDefectLinear]
          · simp [splitBoxedReadout, splitBoxedRows, blockDefectLinear, hij]

/-- The rows of every matrix with the displayed split boxed shape are linearly
independent. No condition on `c`, `ell`, `a`, or the off-diagonal coefficients
is needed. -/
theorem splitBoxedRows_linearIndependent
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) :
    LinearIndependent K (splitBoxedRows c ell a b) := by
  have hstandard := (Pi.basisFun K (Option (Fin m))).linearIndependent
  have himage :
      LinearIndependent K (splitBoxedReadout c ell ∘ splitBoxedRows c ell a b) := by
    convert hstandard using 1
    funext i
    rw [Function.comp_apply, splitBoxedReadout_splitBoxedRows, Pi.basisFun_apply]
  exact LinearIndependent.of_comp (splitBoxedReadout c ell) himage

theorem splitBlockRowInner_comm {m : ℕ} (R S : SplitBlockRow K m) :
    splitBlockRowInner R S = splitBlockRowInner S R := by
  simp [splitBlockRowInner, splitBlockInner, dot_comm]

theorem splitBlockRowBilin_isRefl {m : ℕ} :
    (splitBlockRowBilin (K := K) (m := m)).IsRefl := by
  intro R S hRS
  rw [splitBlockRowBilin_apply] at hRS ⊢
  rw [splitBlockRowInner_comm]
  exact hRS

theorem splitBlockRowBilin_separatingLeft {m : ℕ} :
    LinearMap.SeparatingLeft (splitBlockRowBilin (K := K) (m := m)) := by
  classical
  intro R hR
  funext j k
  cases j with
  | none =>
      have h := hR (Pi.single none (Pi.single k (1 : K)))
      fin_cases k <;>
        simpa [splitBlockRowBilin, splitBlockRowInner, splitBlockInner,
          dot, Pi.single_apply] using h
  | some j =>
      have h := hR (Pi.single (some j) (Pi.single k (1 : K)))
      rw [splitBlockRowBilin_apply, splitBlockRowInner,
        Fintype.sum_option] at h
      rw [Fintype.sum_eq_single j (fun x hx => by
        simp [splitBlockInner, dot, hx])] at h
      fin_cases k <;>
        simpa [splitBlockInner, dot, Pi.single_apply] using h

theorem splitBlockRowBilin_separatingRight {m : ℕ} :
    LinearMap.SeparatingRight (splitBlockRowBilin (K := K) (m := m)) := by
  classical
  intro R hR
  funext j k
  cases j with
  | none =>
      have h := hR (Pi.single none (Pi.single k (1 : K)))
      fin_cases k <;>
        simpa [splitBlockRowBilin, splitBlockRowInner, splitBlockInner,
          dot, Pi.single_apply] using h
  | some j =>
      have h := hR (Pi.single (some j) (Pi.single k (1 : K)))
      rw [splitBlockRowBilin_apply, splitBlockRowInner,
        Fintype.sum_option] at h
      rw [Fintype.sum_eq_single j (fun x hx => by
        simp [splitBlockInner, dot, hx])] at h
      fin_cases k <;>
        simpa [splitBlockInner, dot, Pi.single_apply] using h

theorem splitBlockRowBilin_nondegenerate {m : ℕ} :
    (splitBlockRowBilin (K := K) (m := m)).Nondegenerate := by
  exact ⟨splitBlockRowBilin_separatingLeft, splitBlockRowBilin_separatingRight⟩

theorem splitBoxedRows_rowSpace_finrank
    {m : ℕ} (c : K) (ell : Fin m → SplitBlock K) (a : Fin m → K)
    (b : Fin m → Fin m → K) :
    Module.finrank K ↥(splitBoxedRowSpace (splitBoxedRows c ell a b)) = m + 1 := by
  let hlin := splitBoxedRows_linearIndependent c ell a b
  let e : ↥(splitBoxedRowSpace (splitBoxedRows c ell a b)) ≃ₗ[K]
      (Option (Fin m) →₀ K) :=
    LinearEquiv.ofBijective (hlin.repr)
      ⟨(LinearMap.ker_eq_bot.mp hlin.repr_ker),
        (LinearMap.range_eq_top.mp hlin.repr_range)⟩
  calc
    Module.finrank K ↥(splitBoxedRowSpace (splitBoxedRows c ell a b)) =
        Module.finrank K (Option (Fin m) →₀ K) := LinearEquiv.finrank_eq e
    _ = Fintype.card (Option (Fin m)) := by simp
    _ = m + 1 := by simp

end BuildingUpFormalization.Components.SplitBoxed
