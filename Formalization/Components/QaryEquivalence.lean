import Formalization.Components.QaryEquivalenceDefinitions
import Formalization.Components.QaryForward

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryEquivalence

open BuildingUpFormalization.Components.Foundations
open BuildingUpFormalization.Components.QaryForward

variable {K : Type*} [Field K]

/-- Exact two-way equivalence for the q-ary bordered boxed family with a free
lower-right core.  Child self-duality is equivalent to the Kim--Lee norm and
coefficient equations together with self-duality of the unrestricted core.
Under these conditions the boxed family is literally `buildRows`, and deleting
the distinguished head pair recovers `G` exactly. -/
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
  constructor
  · intro hchild
    have hchild' : paperSelfDualCode (K := K)
        (rowSpace (qaryAdaptedFamily x c Y G)) := by
      simpa [qaryFreeCoreBoxedFamily] using hchild
    rcases paper_qary_adapted_reduction (K := K) hc hchild' with
      ⟨hx, hY, _hlinChild, _hlinG, _hdimG, hparent, heq⟩
    have hboxed : qaryFreeCoreBoxedFamily x c Y G = buildRows x c G := by
      simpa [qaryFreeCoreBoxedFamily] using heq
    have hdelete : deleteHyperbolicPairSplit (K := K)
        (qaryFreeCoreBoxedFamily x c Y G) = G := by
      rw [hboxed]
      exact deleteHyperbolicPairSplit_buildRows (K := K) x c G
    exact ⟨hx, hY, hparent, hboxed, hdelete⟩
  · rintro ⟨hx, _hY, hparent, hboxed, _hdelete⟩
    have hcneg : (-c) ^ 2 = (-1 : K) := by
      calc
        (-c) ^ 2 = c ^ 2 := by ring
        _ = (-1 : K) := hc
    have hbuild : paperSelfDualCode (K := K) (rowSpace (buildRows x c G)) := by
      simpa using
        (paper_qary_kim_lee_building_up_exact
          (K := K) (x := x) (c := -c) (G := G) hx hcneg hparent)
    rw [hboxed]
    exact hbuild

end BuildingUpFormalization.Components.QaryEquivalence
