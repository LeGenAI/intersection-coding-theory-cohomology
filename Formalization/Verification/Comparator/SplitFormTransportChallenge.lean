import Formalization.Components.SplitFormTransportDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.SplitFormTransport

open BuildingUpFormalization.Components.Foundations
variable {K : Type*} [Field K]

theorem split_form_transport_exact {n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (hc : c ^ 2 = (-1 : K))
    (C : Submodule K (Fin (2 + n) → K)) :
    let e := headAlignLinearEquiv (K := K) (n := n) c hc
    (∀ v, e v = prepend2 ((v 0 - c * v 1) / 2)
      ((v 0 + c * v 1) / 2) (splitTail (K := K) v)) ∧
    IsFormIsometry (dotBilin (K := K)) (splitTargetBilin (K := K)) e ∧
    (paperSelfDualCode (K := K) C ↔
      IsSelfOrthogonal (splitTargetBilin (K := K)) (C.map e.toLinearMap)) := by
  sorry

theorem split_isometry_code_equiv_exact
    {m₁ m₂ n : ℕ} [Fact ((2 : K) ≠ 0)] (c : K)
    (R : Fin m₁ → Fin (2 + n) → K) (S : Fin m₂ → Fin (2 + n) → K) :
    SplitIsometryCodeEquiv (K := K) c R S ↔
      ∃ e : (Fin (2 + n) → K) ≃ₗ[K] (Fin (2 + n) → K),
        (∀ v, splitTail (K := K) (e v) = splitTail (K := K) v) ∧
        (∀ x, e (prepend2 1 c x) = r0 x) ∧
        (∀ g, e (prepend2 0 0 g) = prepend2 0 0 g) ∧
        (∀ u v, (2 : K) * ((e u) 0 * (e v) 1 + (e u) 1 * (e v) 0) +
          dot (splitTail (K := K) (e u)) (splitTail (K := K) (e v)) = dot u v) ∧
        (rowSpace R).map e.toLinearMap = rowSpace S := by
  sorry

theorem head_alignment_not_euclidean_isometry
    {n : ℕ} [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    ¬ IsFormIsometry (dotBilin (K := K)) (dotBilin (K := K))
      (headAlignLinearEquiv (K := K) (n := n) c hc) := by
  sorry

end BuildingUpFormalization.Components.SplitFormTransport

