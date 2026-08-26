import Formalization.Components.QaryEquivalenceDefinitions
import Formalization.Components.QaryForward

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryEquivalence

open BuildingUpFormalization.Components.Foundations
open BuildingUpFormalization.Components.QaryForward

variable {K : Type*} [Field K]

theorem paper_qary_free_core_boxed_equivalence
    {m : ℕ} {x : Fin (2 * m) → K} {c : K}
    {Y : Fin m → K} {G : Fin m → Fin (2 * m) → K}
    (hc : c ^ 2 = (-1 : K)) :
    paperSelfDualCode (K := K)
        (rowSpace (qaryFreeCoreBoxedFamily x c Y G)) ↔
      dot x x = (-1 : K) ∧
      (∀ i : Fin m, Y i = dot x (G i)) ∧
      paperSelfDualCode (K := K) (rowSpace G) ∧
      qaryFreeCoreBoxedFamily x c Y G = buildRows x c G ∧
      deleteHyperbolicPairSplit (K := K)
        (qaryFreeCoreBoxedFamily x c Y G) = G := by
  sorry

end BuildingUpFormalization.Components.QaryEquivalence
