import Formalization.Components.QaryForwardDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryForward

variable {K : Type*} [Field K]

@[simp] theorem buildSuccLinear_apply
    {n : ℕ} (x g : Fin n → K) (c : K) :
    buildSuccLinear x c g = ri c (dot x g) g := by
  sorry

@[simp] theorem splitTailLinear_buildSuccLinear
    {n : ℕ} (x : Fin n → K) (c : K) (g : Fin n → K) :
    splitTailLinear (K := K) (buildSuccLinear x c g) = g := by
  sorry

theorem buildRows_succ_eq_buildSuccLinear
    {m n : ℕ} (x : Fin n → K) (c : K) (G : Fin m → Fin n → K)
    (i : Fin m) :
    buildRows x c G (Fin.succ i) = buildSuccLinear x c (G i) := by
  sorry

theorem buildRows_tail_linearIndependent
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hbuild : LinearIndependent K (buildRows x c G)) :
    LinearIndependent K G := by
  sorry

theorem buildRows_linearIndependent_iff
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K)) :
    LinearIndependent K (buildRows x c G) ↔ LinearIndependent K G := by
  sorry

theorem dot_ri_ri_eq_dot
    {n : ℕ} {g h : Fin n → K} {c yi yj : K}
    (hc : c ^ 2 = (-1 : K)) :
    dot (ri c yi g) (ri c yj h) = dot g h := by
  sorry

theorem buildRows_tail_pairwiseOrthogonal
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K))
    (hbuild : PairwiseOrthogonal (K := K) (buildRows x c G)) :
    PairwiseOrthogonal (K := K) G := by
  sorry

theorem buildRows_pairwiseOrthogonal_iff
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hx : dot x x = (-1 : K))
    (hc : c ^ 2 = (-1 : K)) :
    PairwiseOrthogonal (K := K) (buildRows x c G) ↔
      PairwiseOrthogonal (K := K) G := by
  sorry

theorem paper_qary_kim_lee_building_up_exact
    {m : ℕ} {x : Fin (2 * m) → K} {c : K}
    {G : Fin m → Fin (2 * m) → K}
    (hx : dot x x = (-1 : K))
    (hc : c ^ 2 = (-1 : K))
    (hparent : paperSelfDualCode (K := K) (rowSpace G)) :
    paperSelfDualCode (K := K) (rowSpace (buildRows x (-c) G)) := by
  sorry

theorem rowSpace_finrank_of_linearIndependent
    {m n : ℕ} {G : Fin m → Fin n → K}
    (hG : LinearIndependent K G) :
    Module.finrank K ↥(rowSpace G) = m := by
  sorry

theorem buildRows_tail_finrank_of_linearIndependent
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hbuild : LinearIndependent K (buildRows x c G)) :
    Module.finrank K ↥(rowSpace G) = m := by
  sorry

theorem buildRows_tail_independent_orthogonal_finrank
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K))
    (hlin : LinearIndependent K (buildRows x c G))
    (horth : PairwiseOrthogonal (K := K) (buildRows x c G)) :
    LinearIndependent K G ∧
      PairwiseOrthogonal (K := K) G ∧
      Module.finrank K ↥(rowSpace G) = m := by
  sorry

theorem buildRows_tail_paperLagrangianSubspace
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K))
    (hlin : LinearIndependent K (buildRows x c G))
    (horth : PairwiseOrthogonal (K := K) (buildRows x c G))
    (hcard : 2 * m = n) :
    paperLagrangianSubspace (K := K) (rowSpace G) := by
  sorry

theorem dot_r0_r0_eq_zero_iff
    {n : ℕ} {x : Fin n → K} :
    dot (r0 x) (r0 x) = 0 ↔ dot x x = (-1 : K) := by
  sorry

theorem dot_r0_ri_eq_zero_iff
    {n : ℕ} {x g : Fin n → K} {c yi : K} :
    dot (r0 x) (ri c yi g) = 0 ↔ yi = dot x g := by
  sorry

theorem qaryAdaptedFamily_extension_vector_norm
    {m n : ℕ} {x : Fin n → K} {c : K}
    {Y : Fin m → K} {G : Fin m → Fin n → K}
    (horth : PairwiseOrthogonal (K := K) (qaryAdaptedFamily x c Y G)) :
    dot x x = (-1 : K) := by
  sorry

theorem qaryAdaptedFamily_coefficient_eq_dot
    {m n : ℕ} {x : Fin n → K} {c : K}
    {Y : Fin m → K} {G : Fin m → Fin n → K}
    (horth : PairwiseOrthogonal (K := K) (qaryAdaptedFamily x c Y G)) :
    ∀ i : Fin m, Y i = dot x (G i) := by
  sorry

theorem qaryAdaptedFamily_eq_buildRows
    {m n : ℕ} {x : Fin n → K} {c : K}
    {Y : Fin m → K} {G : Fin m → Fin n → K}
    (hY : ∀ i : Fin m, Y i = dot x (G i)) :
    qaryAdaptedFamily x c Y G = buildRows x c G := by
  sorry

theorem qaryAdaptedFamily_linearIndependent_of_paperSelfDualCode
    {m : ℕ} {x : Fin (2 * m) → K} {c : K}
    {Y : Fin m → K} {G : Fin m → Fin (2 * m) → K}
    (hself : paperSelfDualCode (K := K) (rowSpace (qaryAdaptedFamily x c Y G))) :
    LinearIndependent K (qaryAdaptedFamily x c Y G) := by
  sorry

theorem qaryAdaptedFamily_tail_paperSelfDualCode
    {m : ℕ} {x : Fin (2 * m) → K} {c : K}
    {Y : Fin m → K} {G : Fin m → Fin (2 * m) → K}
    (hc : c ^ 2 = (-1 : K))
    (hself : paperSelfDualCode (K := K) (rowSpace (qaryAdaptedFamily x c Y G))) :
    paperSelfDualCode (K := K) (rowSpace G) := by
  sorry

theorem paper_qary_adapted_reduction
    {m : ℕ} {x : Fin (2 * m) → K} {c : K}
    {Y : Fin m → K} {G : Fin m → Fin (2 * m) → K}
    (hc : c ^ 2 = (-1 : K))
    (hself : paperSelfDualCode (K := K) (rowSpace (qaryAdaptedFamily x c Y G))) :
    dot x x = (-1 : K) ∧
      (∀ i : Fin m, Y i = dot x (G i)) ∧
      LinearIndependent K (qaryAdaptedFamily x c Y G) ∧
      LinearIndependent K G ∧
      Module.finrank K ↥(rowSpace G) = m ∧
      paperSelfDualCode (K := K) (rowSpace G) ∧
      qaryAdaptedFamily x c Y G = buildRows x c G := by
  sorry

end BuildingUpFormalization.Components.QaryForward
