import Formalization.Components.QaryForwardDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryEquivalence

open BuildingUpFormalization.Components.QaryForward

variable {K : Type*} [Field K]

/-- The q-ary bordered boxed family with an unrestricted lower-right core
`G`.  No diagonal, triangular, or recursive boxed condition is imposed on
`G`; the only restrictions on the core occur in the equivalence theorem. -/
def qaryFreeCoreBoxedFamily {m n : ℕ}
    (x : Fin n → K) (c : K) (Y : Fin m → K)
    (G : Fin m → Fin n → K) :
    Fin (m + 1) → Fin (2 + n) → K :=
  qaryAdaptedFamily x c Y G

end BuildingUpFormalization.Components.QaryEquivalence
