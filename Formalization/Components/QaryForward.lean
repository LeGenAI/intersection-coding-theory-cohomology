import Formalization.Components.QaryForwardDefinitions
import Formalization.Components.Foundations

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryForward

open BuildingUpFormalization.Components.Foundations

variable {K : Type*} [Field K]

@[simp] theorem buildSuccLinear_apply
    {n : ℕ} (x g : Fin n → K) (c : K) :
    buildSuccLinear x c g = ri c (dot x g) g := by
  rfl

@[simp] theorem splitTailLinear_buildSuccLinear
    {n : ℕ} (x : Fin n → K) (c : K) (g : Fin n → K) :
    splitTailLinear (K := K) (buildSuccLinear x c g) = g := by
  simp [buildSuccLinear, splitTail_ri]

theorem buildRows_succ_eq_buildSuccLinear
    {m n : ℕ} (x : Fin n → K) (c : K) (G : Fin m → Fin n → K)
    (i : Fin m) :
    buildRows x c G (Fin.succ i) = buildSuccLinear x c (G i) := by
  rfl

/-- Converse: independence of the extended building-up rows
forces independence of the parent (tail) rows.  No dimension count is used. -/
theorem buildRows_tail_linearIndependent
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hbuild : LinearIndependent K (buildRows x c G)) :
    LinearIndependent K G := by
  have hsucc :
      LinearIndependent K (fun i : Fin m ↦ buildRows x c G (Fin.succ i)) := by
    simpa only [Function.comp_apply] using
      hbuild.comp Fin.succ (Fin.succ_injective m)
  have himage : LinearIndependent K (buildSuccLinear x c ∘ G) := by
    simpa only [Function.comp_apply, buildRows_succ_eq_buildSuccLinear] using hsucc
  exact LinearIndependent.of_comp (buildSuccLinear x c) himage

theorem buildRows_linearIndependent_iff
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K)) :
    LinearIndependent K (buildRows x c G) ↔ LinearIndependent K G := by
  constructor
  · exact buildRows_tail_linearIndependent
  · exact buildRows_linearIndependent_of_linearIndependent (K := K) hc

/-- Under `c² = -1`, the correction coordinates contribute zero, so the
successor-row inner product is exactly the parent-row inner product. -/
theorem dot_ri_ri_eq_dot
    {n : ℕ} {g h : Fin n → K} {c yi yj : K}
    (hc : c ^ 2 = (-1 : K)) :
    dot (ri c yi g) (ri c yj h) = dot g h := by
  rw [dot_ri_ri_expand, hc]
  ring

/-- Converse for orthogonality of the parent rows. -/
theorem buildRows_tail_pairwiseOrthogonal
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K))
    (hbuild : PairwiseOrthogonal (K := K) (buildRows x c G)) :
    PairwiseOrthogonal (K := K) G := by
  intro i j
  have hij := hbuild (Fin.succ i) (Fin.succ j)
  simpa only [buildRows, Fin.cases_succ, dot_ri_ri_eq_dot hc] using hij

theorem buildRows_pairwiseOrthogonal_iff
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hx : dot x x = (-1 : K))
    (hc : c ^ 2 = (-1 : K)) :
    PairwiseOrthogonal (K := K) (buildRows x c G) ↔
      PairwiseOrthogonal (K := K) G := by
  constructor
  · exact buildRows_tail_pairwiseOrthogonal hc
  · exact buildRows_pairwiseOrthogonal (K := K) hx hc

/-- Exact forward theorem printed as Kim--Lee Proposition 2.1 in the paper.
The source convention uses rows `(-y_i, c y_i, g_i)`; since the internal
`buildRows x d G` convention is `(-y_i, -d y_i, g_i)`, the literal displayed
family is `buildRows x (-c) G`. -/
theorem paper_qary_kim_lee_building_up_exact
    {m : ℕ} {x : Fin (2 * m) → K} {c : K}
    {G : Fin m → Fin (2 * m) → K}
    (hx : dot x x = (-1 : K))
    (hc : c ^ 2 = (-1 : K))
    (hparent : paperSelfDualCode (K := K) (rowSpace G)) :
    paperSelfDualCode (K := K) (rowSpace (buildRows x (-c) G)) := by
  have hcneg : (-c) ^ 2 = (-1 : K) := by
    calc
      (-c) ^ 2 = c ^ 2 := by ring
      _ = (-1 : K) := hc
  have horth : ∀ i j : Fin m, dot (G i) (G j) = 0 := by
    exact (pairwiseOrthogonal_iff_rowSpace_le_orthogonal (K := K)).2 hparent.le
  have hhalf :=
    (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
      (K := K) (C := rowSpace G)).mp hparent |>.2
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hhalf
  have hdim : Module.finrank K ↥(rowSpace G) = m := by
    omega
  have hlin : LinearIndependent K G := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simpa [rowSpace] using hdim.symm
  have heven : Even (2 * m) := by
    exact ⟨m, by omega⟩
  have hcard : m + 1 = (2 * m + 2) / 2 := by
    omega
  simpa [paperSelfDualCode] using
    paper_qary_building_up_forward_self_dual
      (K := K) (hx := hx) (hc := hcneg) (hGorth := horth)
      (hGlin := hlin) (heven := heven) (hcard := hcard)

/-- An independent `Fin m`-indexed row family spans an `m`-dimensional row
space. -/
theorem rowSpace_finrank_of_linearIndependent
    {m n : ℕ} {G : Fin m → Fin n → K}
    (hG : LinearIndependent K G) :
    Module.finrank K ↥(rowSpace G) = m := by
  simpa [rowSpace] using finrank_span_eq_card hG

/-- The corrected dimension step: extended-row independence first gives tail
independence, and only then gives the dimension of the parent row space. -/
theorem buildRows_tail_finrank_of_linearIndependent
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hbuild : LinearIndependent K (buildRows x c G)) :
    Module.finrank K ↥(rowSpace G) = m := by
  exact rowSpace_finrank_of_linearIndependent (buildRows_tail_linearIndependent hbuild)

/-- The reverse data package needed by the q-ary proof: the parent rows are
independent and orthogonal, and their span has the advertised dimension. -/
theorem buildRows_tail_independent_orthogonal_finrank
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K))
    (hlin : LinearIndependent K (buildRows x c G))
    (horth : PairwiseOrthogonal (K := K) (buildRows x c G)) :
    LinearIndependent K G ∧
      PairwiseOrthogonal (K := K) G ∧
      Module.finrank K ↥(rowSpace G) = m := by
  exact ⟨buildRows_tail_linearIndependent hlin,
    buildRows_tail_pairwiseOrthogonal hc horth,
    buildRows_tail_finrank_of_linearIndependent hlin⟩

/-- When the number of independent parent rows is half the ambient length,
the recovered parent row space is self-orthogonal (the paper's Lagrangian
condition). -/
theorem buildRows_tail_paperLagrangianSubspace
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K))
    (hlin : LinearIndependent K (buildRows x c G))
    (horth : PairwiseOrthogonal (K := K) (buildRows x c G))
    (hcard : 2 * m = n) :
    paperLagrangianSubspace (K := K) (rowSpace G) := by
  apply (paperLagrangianSubspace_iff_totallyIsotropic_and_finrank_half
    (K := K) (L := rowSpace G)).2
  refine ⟨?_, ?_⟩
  · exact rowSpace_le_orthogonal_of_pairwiseOrthogonal (K := K)
      (buildRows_tail_pairwiseOrthogonal hc horth)
  · rw [buildRows_tail_finrank_of_linearIndependent hlin,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact hcard

theorem dot_r0_r0_eq_zero_iff
    {n : ℕ} {x : Fin n → K} :
    dot (r0 x) (r0 x) = 0 ↔ dot x x = (-1 : K) := by
  rw [r0, dot_prepend2_prepend2]
  constructor
  · intro h
    linear_combination h
  · intro h
    rw [h]
    ring

theorem dot_r0_ri_eq_zero_iff
    {n : ℕ} {x g : Fin n → K} {c yi : K} :
    dot (r0 x) (ri c yi g) = 0 ↔ yi = dot x g := by
  rw [r0, ri, dot_prepend2_prepend2]
  constructor
  · intro h
    have h' : -yi + dot x g = 0 := by simpa using h
    have hneg : -yi = -(dot x g) := eq_neg_of_add_eq_zero_left h'
    simpa using congrArg Neg.neg hneg
  · intro h
    rw [h]
    ring

theorem qaryAdaptedFamily_extension_vector_norm
    {m n : ℕ} {x : Fin n → K} {c : K}
    {Y : Fin m → K} {G : Fin m → Fin n → K}
    (horth : PairwiseOrthogonal (K := K) (qaryAdaptedFamily x c Y G)) :
    dot x x = (-1 : K) := by
  have h := horth 0 0
  simpa only [qaryAdaptedFamily, Fin.cases_zero, dot_r0_r0_eq_zero_iff] using h

theorem qaryAdaptedFamily_coefficient_eq_dot
    {m n : ℕ} {x : Fin n → K} {c : K}
    {Y : Fin m → K} {G : Fin m → Fin n → K}
    (horth : PairwiseOrthogonal (K := K) (qaryAdaptedFamily x c Y G)) :
    ∀ i : Fin m, Y i = dot x (G i) := by
  intro i
  have h := horth 0 (Fin.succ i)
  simpa only [qaryAdaptedFamily, Fin.cases_zero, Fin.cases_succ,
    dot_r0_ri_eq_zero_iff] using h

theorem qaryAdaptedFamily_eq_buildRows
    {m n : ℕ} {x : Fin n → K} {c : K}
    {Y : Fin m → K} {G : Fin m → Fin n → K}
    (hY : ∀ i : Fin m, Y i = dot x (G i)) :
    qaryAdaptedFamily x c Y G = buildRows x c G := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp only [qaryAdaptedFamily, buildRows, Fin.cases_succ]
    rw [hY j]

theorem qaryAdaptedFamily_linearIndependent_of_paperSelfDualCode
    {m : ℕ} {x : Fin (2 * m) → K} {c : K}
    {Y : Fin m → K} {G : Fin m → Fin (2 * m) → K}
    (hself : paperSelfDualCode (K := K) (rowSpace (qaryAdaptedFamily x c Y G))) :
    LinearIndependent K (qaryAdaptedFamily x c Y G) := by
  have hhalf :=
    (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
      (K := K) (C := rowSpace (qaryAdaptedFamily x c Y G))).mp hself |>.2
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hhalf
  have hdim :
      Module.finrank K ↥(rowSpace (qaryAdaptedFamily x c Y G)) = m + 1 := by
    omega
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  simpa [rowSpace] using hdim.symm

theorem qaryAdaptedFamily_tail_paperSelfDualCode
    {m : ℕ} {x : Fin (2 * m) → K} {c : K}
    {Y : Fin m → K} {G : Fin m → Fin (2 * m) → K}
    (hc : c ^ 2 = (-1 : K))
    (hself : paperSelfDualCode (K := K) (rowSpace (qaryAdaptedFamily x c Y G))) :
    paperSelfDualCode (K := K) (rowSpace G) := by
  have horth : PairwiseOrthogonal (K := K) (qaryAdaptedFamily x c Y G) :=
    (pairwiseOrthogonal_iff_rowSpace_le_orthogonal (K := K)).2 hself.le
  have hY := qaryAdaptedFamily_coefficient_eq_dot horth
  have heq := qaryAdaptedFamily_eq_buildRows (c := c) hY
  have hlinBuild : LinearIndependent K (buildRows x c G) := by
    rw [← heq]
    exact qaryAdaptedFamily_linearIndependent_of_paperSelfDualCode hself
  have horthBuild : PairwiseOrthogonal (K := K) (buildRows x c G) := by
    rw [← heq]
    exact horth
  simpa [paperSelfDualCode, paperLagrangianSubspace] using
    buildRows_tail_paperLagrangianSubspace hc hlinBuild horthBuild rfl

/-- Exact paper-facing reverse theorem for Theorem 3.9.  Starting from the
displayed adapted generator family with arbitrary coefficients, child
self-duality forces the extension-vector norm, the Kim--Lee coefficients,
linear independence and the dimension of the tails, tail self-duality, and
literal agreement with `buildRows`. -/
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
  have horth : PairwiseOrthogonal (K := K) (qaryAdaptedFamily x c Y G) :=
    (pairwiseOrthogonal_iff_rowSpace_le_orthogonal (K := K)).2 hself.le
  have hx := qaryAdaptedFamily_extension_vector_norm horth
  have hY := qaryAdaptedFamily_coefficient_eq_dot horth
  have heq := qaryAdaptedFamily_eq_buildRows (c := c) hY
  have hlinAdapted := qaryAdaptedFamily_linearIndependent_of_paperSelfDualCode hself
  have hlinBuild : LinearIndependent K (buildRows x c G) := by
    rw [← heq]
    exact hlinAdapted
  have hlinG := buildRows_tail_linearIndependent hlinBuild
  have hdimG := rowSpace_finrank_of_linearIndependent hlinG
  have hselfG := qaryAdaptedFamily_tail_paperSelfDualCode hc hself
  exact ⟨hx, hY, hlinAdapted, hlinG, hdimG, hselfG, heq⟩

end BuildingUpFormalization.Components.QaryForward
