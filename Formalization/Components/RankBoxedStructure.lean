import Formalization.Components.RankBoxedStructureDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RankBoxedStructure

open BuildingUpFormalization.Components.SplitBoxed
open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.QaryRankBoxedNormalization

variable {K : Type*} [Field K]

/-- Exact repeated-subbox statement, including the literal restricted rows,
the same core, both restricted Gram laws, and self-duality. -/
theorem paper_rankBoxed_pivot_restriction_exact {l k r : ℕ}
    (s : Fin l ↪ Fin k) (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D) (hpp : PivotGramRelations c P H Q) :
    let R := restrictRankBoxRows s (rankBoxedRows c P H Q A D)
    R = rankBoxedRows c (fun i j => P (s i) (s j))
      (fun i t => H (s i) t) (fun i t => Q (s i) t)
      (fun t j => A t (s j)) D ∧
    PivotMasterRelations (fun i t => Q (s i) t) (fun t j => A t (s j)) D ∧
    PivotGramRelations c (fun i j => P (s i) (s j))
      (fun i t => H (s i) t) (fun i t => Q (s i) t) ∧
    RankBoxedPairwiseOrthogonal R ∧ LinearIndependent K R ∧
    rankBoxedRowSpace R =
      (rankBoxRowBilin (K := K) (k := l) (r := r)).orthogonal
        (rankBoxedRowSpace R) := by
  dsimp only
  have heq :
      restrictRankBoxRows s (rankBoxedRows c P H Q A D) =
        rankBoxedRows c (fun i j => P (s i) (s j))
          (fun i t => H (s i) t) (fun i t => Q (s i) t)
          (fun t j => A t (s j)) D := by
    funext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp [restrictRankBoxRows, keepRankBoxIndex, rankBoxedRows, s.injective.eq_iff]
      | inr j => rfl
    | inr i => cases j <;> rfl
  have hpm' : PivotMasterRelations (fun i t => Q (s i) t)
      (fun t j => A t (s j)) D := fun t i => hpm t (s i)
  have hpp' : PivotGramRelations c (fun i j => P (s i) (s j))
      (fun i t => H (s i) t) (fun i t => Q (s i) t) := by
    intro i j
    simpa [s.injective.eq_iff] using hpp (s i) (s j)
  refine ⟨heq, hpm', hpp', ?_⟩
  rw [heq]
  exact rankBoxedRows_forward_selfDual c _ _ _ _ D
    (by simpa [pow_two] using hc) hD hpm' hpp'

/-- Exact terminal code after all pivot rows have been removed. -/
theorem paper_rankBoxed_terminal_exact {r : ℕ} (c : K)
    (P : Fin 0 → Fin 0 → K) (H Q : Fin 0 → Fin r → K)
    (A : Fin r → Fin 0 → K) (D : Fin r → Fin r → K)
    (hD : RankBoxCoreFullRank D) :
    rankBoxedRowSpace (rankBoxedRows c P H Q A D) =
      qaryIsotropicLineCode (K := K) c := by
  classical
  let F : (Fin r → K) →ₗ[K] RankBoxRow K 0 r :=
    { toFun := fun w j => match j with
        | .inl i => Fin.elim0 i
        | .inr t => isotropicLineBlock c (w t)
      map_add' := by
        intro u v
        funext j q
        cases j with
        | inl i => exact Fin.elim0 i
        | inr t =>
          fin_cases q <;> simp [isotropicLineBlock, head2, mul_add]
      map_smul' := by
        intro a v
        funext j q
        cases j with
        | inl i => exact Fin.elim0 i
        | inr t =>
          fin_cases q <;> simp [isotropicLineBlock, head2, mul_left_comm] }
  have hFD : ∀ s, F (D s) = rankBoxedRows c P H Q A D (.inr s) := by
    intro s
    funext j
    cases j with
    | inl i => exact Fin.elim0 i
    | inr t => rfl
  have hDli : LinearIndependent K D :=
    Matrix.linearIndependent_rows_of_det_ne_zero hD
  have hspanD : Submodule.span K (Set.range D) = ⊤ :=
    hDli.span_eq_top_of_card_eq_finrank' (by simp)
  apply le_antisymm
  · rw [rankBoxedRowSpace, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    change qaryBlockDefectLinear c (rankBoxedRows c P H Q A D x) = 0
    funext j
    cases x with
    | inl i => exact Fin.elim0 i
    | inr s =>
      cases j with
      | inl i => exact Fin.elim0 i
      | inr t =>
        simp [qaryBlockDefectLinear, rankBoxedRows]
  · intro v hv
    let w : Fin r → K := fun t => v (.inr t) 0
    have hw : w ∈ Submodule.span K (Set.range D) := by rw [hspanD]; trivial
    have hFw : F w ∈ rankBoxedRowSpace (rankBoxedRows c P H Q A D) := by
      refine Submodule.span_induction
        (p := fun x _ => F x ∈ rankBoxedRowSpace (rankBoxedRows c P H Q A D))
        ?_ ?_ ?_ ?_ hw
      · intro x hx
        obtain ⟨s, rfl⟩ := hx
        rw [hFD]
        exact Submodule.subset_span ⟨.inr s, rfl⟩
      · simpa using
          (rankBoxedRowSpace (rankBoxedRows c P H Q A D)).zero_mem
      · intro x y hx hy ihx ihy
        simpa using (rankBoxedRowSpace (rankBoxedRows c P H Q A D)).add_mem ihx ihy
      · intro a x hx ih
        simpa using (rankBoxedRowSpace (rankBoxedRows c P H Q A D)).smul_mem a ih
    have hFv : F w = v := by
      funext j q
      cases j with
      | inl i => exact Fin.elim0 i
      | inr t =>
        have ht := congrFun (show qaryBlockDefectLinear c v = 0 from hv) (.inr t)
        change v (.inr t) 1 - c * v (.inr t) 0 = 0 at ht
        fin_cases q
        · rfl
        · change c * v (.inr t) 0 = v (.inr t) 1
          exact (sub_eq_zero.mp ht).symm
    rwa [hFv] at hFw

/-- Literal matrix equality and iff of the full hypothesis sets in the
transition from Theorem 3.12 to Theorem 3.13. -/
theorem paper_rankOne_split_specialization_exact {k : ℕ}
    (c : K) (ell : Fin k → SplitBlock K)
    (a : Fin k → K) (b : Fin k → Fin k → K)
    (hc : c ^ 2 = (-1 : K)) :
    rankBoxedRows c (specializationP b) (specializationH ell)
      (specializationQ c ell) (specializationA a) (unitCore (K := K)) =
      (fun i j => splitBoxedRows c ell a b
        (rankOneOptionEquiv k i) (rankOneOptionEquiv k j)) ∧
    ((RankBoxCoreFullRank (unitCore (K := K)) ∧
      PivotMasterRelations (specializationQ c ell) (specializationA a) unitCore ∧
      PivotGramRelations c (specializationP b) (specializationH ell)
        (specializationQ c ell)) ↔
      ((∀ i, dot (ell i) (ell i) = (-1 : K)) ∧
       (∀ i, ell i 0 + c * ell i 1 = -c * a i) ∧
       (∀ i j, i < j → c * (b i j + b j i) + dot (ell i) (ell j) = 0))) := by
  classical
  have hc_mul : c * c = (-1 : K) := by simpa [pow_two] using hc
  have hc_ne : c ≠ 0 := by intro h; subst c; simp at hc
  have hell (i : Fin k) :
      splitAffineBlock c (ell i 0) (ell i 1 - c * ell i 0) = ell i := by
    funext q
    fin_cases q <;> simp [splitAffineBlock, head2]
  have hdot (i j : Fin k) :
      c * (ell i 0 * (ell j 1 - c * ell j 0) +
        (ell i 1 - c * ell i 0) * ell j 0) +
        (ell i 1 - c * ell i 0) * (ell j 1 - c * ell j 0) =
        dot (ell i) (ell j) := by
    have h := splitBlockInner_splitAffineBlock_of_sq_neg_one c
      (ell i 0) (ell i 1 - c * ell i 0)
      (ell j 0) (ell j 1 - c * ell j 0) hc_mul
    rw [hell i, hell j] at h
    exact h.symm
  have hentry (i : Fin k) :
      c * (a i + (ell i 1 - c * ell i 0)) =
        c * a i + (ell i 0 + c * ell i 1) := by
    calc
      _ = c * a i + c * ell i 1 - c ^ 2 * ell i 0 := by ring
      _ = _ := by rw [hc]; ring
  have hpm_iff :
      PivotMasterRelations (specializationQ c ell) (specializationA a) unitCore ↔
        ∀ i, ell i 0 + c * ell i 1 = -c * a i := by
    constructor
    · intro h i
      have hi := h 0 i
      simp [specializationQ, specializationA, unitCore] at hi
      have hh := hentry i
      rw [hi, mul_zero] at hh
      linear_combination -hh
    · intro h s i
      simp only [specializationQ, specializationA, unitCore, mul_one,
        Fintype.sum_unique]
      have hh := hentry i
      rw [h i] at hh
      simp only [neg_mul, add_neg_cancel] at hh
      exact (mul_eq_zero.mp hh).resolve_left hc_ne
  have hpp_iff :
      PivotGramRelations c (specializationP b) (specializationH ell)
        (specializationQ c ell) ↔
        ((∀ i, dot (ell i) (ell i) = (-1 : K)) ∧
         (∀ i j, i < j → c * (b i j + b j i) + dot (ell i) (ell j) = 0)) := by
    unfold PivotGramRelations specializationH specializationQ
    simp only [Fintype.sum_unique, hdot]
    constructor
    · intro h
      constructor
      · intro i
        have hi := h i i
        simp [specializationP] at hi
        linear_combination hi
      · intro i j hij
        simpa [specializationP, ne_of_lt hij, (ne_of_lt hij).symm] using h i j
    · rintro ⟨hnorm, hoff⟩ i j
      by_cases hij : i = j
      · subst j
        simp [specializationP, hnorm]
      · simp only [specializationP, if_neg hij, if_neg (Ne.symm hij), zero_add]
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · exact hoff i j hlt
        · simpa [add_comm, dot_comm] using hoff j i hgt
  constructor
  · funext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        by_cases hij : i = j
        · subst j
          simp [rankBoxedRows, specializationP, rankOneOptionEquiv,
            splitBoxedRows, splitAffineBlock_zero_one]
        · simp [rankBoxedRows, specializationP, rankOneOptionEquiv,
            splitBoxedRows, hij, splitAffineBlock_alpha_zero]
      | inr t =>
        change splitAffineBlock c (ell i 0) (ell i 1 - c * ell i 0) = ell i
        exact hell i
    | inr s => cases j <;> rfl
  · rw [hpm_iff, hpp_iff]
    have hunit : RankBoxCoreFullRank (unitCore (K := K)) :=
      rankOne_unit_core_fullRank
    tauto

end BuildingUpFormalization.Components.RankBoxedStructure
