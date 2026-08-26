import Formalization.Components.RankBoxedStructureDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RankBoxedExtension

open BuildingUpFormalization.Components.RankBoxed

variable {K : Type*} [Field K]

/-- Prepend one pivot. The old pivot coefficients are retained literally;
the new top row is freely chosen and the first column is forced by the
Gram relation. This definition is used only with `2 ≠ 0` and `c² = -1`. -/
def extendP {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (h q : Fin r → K) (u : Fin k → K) : Fin (k + 1) → Fin (k + 1) → K :=
  Fin.cons
    (Fin.cons (c / 2 * (1 + ∑ t, q t * q t) - ∑ t, h t * q t) u)
    (fun i => Fin.cons
      (c * (∑ t, q t * Q i t) - (∑ t, (h t * Q i t + q t * H i t)) - u i)
      (P i))

/-- The new terminal-by-pivot column is `-D qᵀ`; all old entries remain. -/
def extendA {k r : ℕ} (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K) (q : Fin r → K) : Fin r → Fin (k + 1) → K :=
  fun s => Fin.cons (-(∑ t, q t * D s t)) (A s)

/-- Building-up in the same paired coordinates and with the same `D`. -/
def extendedRows {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (h q : Fin r → K) (u : Fin k → K) :
    RankBoxIndex (k + 1) r → RankBoxRow K (k + 1) r :=
  rankBoxedRows c (extendP c P H Q h q u) (Fin.cons h H) (Fin.cons q Q)
    (extendA A D q) D

end BuildingUpFormalization.Components.RankBoxedExtension
