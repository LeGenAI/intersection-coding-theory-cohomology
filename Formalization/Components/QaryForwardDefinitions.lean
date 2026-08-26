import Formalization.Archive.SubmittedBaseline

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryForward

variable {K : Type*} [Field K]

/-- The linear operation sending a parent row to its successor row in the
q-ary building-up construction.  Making this map explicit lets the reverse
linear-independence argument use `LinearIndependent.of_comp` directly. -/
def buildSuccLinear {n : ℕ} (x : Fin n → K) (c : K) :
    (Fin n → K) →ₗ[K] (Fin (2 + n) → K) where
  toFun g := ri c (dot x g) g
  map_add' g h := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro k
      fin_cases k <;> simp [ri, prepend2, head2, dot_add_right] <;> ring
    · intro k
      simp [ri, prepend2]
  map_smul' a g := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro k
      fin_cases k
      · simp [ri, prepend2, head2, dot_smul_right]
      · simp [ri, prepend2, head2, dot_smul_right]
        ring
    · intro k
      simp [ri, prepend2]

/-- The adapted row family displayed in Theorem 3.9 before orthogonality has
identified the coefficients `Y i` with `dot x (G i)`. -/
def qaryAdaptedFamily {m n : ℕ}
    (x : Fin n → K) (c : K) (Y : Fin m → K) (G : Fin m → Fin n → K) :
    Fin (m + 1) → Fin (2 + n) → K :=
  Fin.cases (r0 x) (fun i => ri c (Y i) (G i))

end BuildingUpFormalization.Components.QaryForward
