import Formalization.Components.FoundationsDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.SplitFormTransport

variable {K : Type*} [Field K]

/-- Target form for the archived head-alignment map.
Its first block has Gram matrix [[0,2],[2,0]], not the Euclidean identity. -/
def splitTargetBilin {n : ℕ} : LinearMap.BilinForm K (Fin (2 + n) → K) :=
  LinearMap.mk₂ K splitDot
    (by intro u v w; simp [splitDot, splitTail, dot, add_mul,
      Finset.sum_add_distrib]; ring)
    (by intro a u v; simp only [splitDot, splitTail, dot, Pi.smul_apply,
      smul_eq_mul]; simp_rw [mul_assoc]; rw [← Finset.mul_sum]; ring)
    (by intro u v w; simp [splitDot, splitTail, dot, mul_add,
      Finset.sum_add_distrib]; ring)
    (by intro a u v; simp only [splitDot, splitTail, dot, Pi.smul_apply,
      smul_eq_mul]; simp_rw [mul_left_comm (u _) a]; rw [← Finset.mul_sum]; ring)

end BuildingUpFormalization.Components.SplitFormTransport
