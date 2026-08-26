import Formalization.Components.SplitFormTransportDefinitions
import Formalization.Components.BinaryCzKim

set_option autoImplicit false

namespace BuildingUpFormalization.Components.SplitFormTransport

open BuildingUpFormalization.Components.Foundations
open BuildingUpFormalization.Components.BinaryCzKim

variable {K : Type*} [Field K]

/-- Source, target, coordinate formula, and self-duality transport are explicit.
This is not a Euclidean code equivalence. -/
theorem split_form_transport_exact {n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (hc : c ^ 2 = (-1 : K))
    (C : Submodule K (Fin (2 + n) → K)) :
    let e := headAlignLinearEquiv (K := K) (n := n) c hc
    (∀ v, e v = prepend2 ((v 0 - c * v 1) / 2)
      ((v 0 + c * v 1) / 2) (splitTail (K := K) v)) ∧
    IsFormIsometry (dotBilin (K := K)) (splitTargetBilin (K := K)) e ∧
    (paperSelfDualCode (K := K) C ↔
      IsSelfOrthogonal (splitTargetBilin (K := K)) (C.map e.toLinearMap)) := by
  dsimp only
  let e := headAlignLinearEquiv (K := K) (n := n) c hc
  have he : IsFormIsometry (dotBilin (K := K)) (splitTargetBilin (K := K)) e :=
    splitDot_headAlignFamilyVec hc
  refine ⟨fun _ => rfl, he, ?_⟩
  constructor
  · exact isSelfOrthogonal_map_of_isFormIsometry he
  · intro hD
    have hinv : IsFormIsometry (splitTargetBilin (K := K)) (dotBilin (K := K))
        e.symm := by
      intro u v
      simpa using (he (e.symm u) (e.symm v)).symm
    have h := isSelfOrthogonal_map_of_isFormIsometry hinv hD
    have hmap : (C.map e.toLinearMap).map e.symm.toLinearMap = C := by
      ext v
      constructor
      · rintro ⟨w, ⟨u, hu, rfl⟩, hv⟩
        have huv : u = v := by simpa using hv
        exact huv ▸ hu
      · intro hv
        exact ⟨e v, ⟨v, hv, rfl⟩, e.symm_apply_apply v⟩
    rw [hmap] at h
    exact h

/-- Expand every clause of the archived predicate, including the different
target form and the image of the actual row space. -/
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
  constructor
  · rintro ⟨e, he, hcode⟩
    refine ⟨e, he.head.tail_eq, he.head.pivot_eq, he.head.zeroHead_eq,
      he.form_eq, ?_⟩
    simpa [SameCode, rowSpace_linearEquivFamily_eq_map] using hcode
  · rintro ⟨e, ht, hp, hz, hf, hcode⟩
    refine ⟨e, ⟨⟨ht, hp, hz⟩, hf⟩, ?_⟩
    simpa [SameCode, rowSpace_linearEquivFamily_eq_map] using hcode

/-- Regression guard: the archived alignment cannot be used as an isometry
of the standard Euclidean form with itself. -/
theorem head_alignment_not_euclidean_isometry
    {n : ℕ} [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    ¬ IsFormIsometry (dotBilin (K := K)) (dotBilin (K := K))
      (headAlignLinearEquiv (K := K) (n := n) c hc) := by
  intro h
  have hp : headAlignLinearEquiv (K := K) (n := n) c hc
      (prepend2 1 c 0) = r0 0 :=
    (headAlignLinearEquiv_hyperbolicBasis c hc 0).1
  have hbad := h (prepend2 1 c 0) (prepend2 1 c 0)
  change dot _ _ = dot _ _ at hbad
  rw [hp] at hbad
  have hc' : c * c = (-1 : K) := by simpa [pow_two] using hc
  rw [r0, dot_prepend2_prepend2, dot_prepend2_prepend2] at hbad
  simpa [dot, hc'] using hbad

end BuildingUpFormalization.Components.SplitFormTransport
