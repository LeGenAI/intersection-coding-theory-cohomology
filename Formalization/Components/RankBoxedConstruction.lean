import Formalization.Components.RankBoxedDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RankBoxed

open BuildingUpFormalization.Components.SplitBoxed

variable {K : Type*} [Field K]

@[simp] theorem splitAffineBlock_apply_zero (c alpha beta : K) :
    splitAffineBlock c alpha beta 0 = alpha := by
  simp [splitAffineBlock, head2]

@[simp] theorem splitAffineBlock_apply_one (c alpha beta : K) :
    splitAffineBlock c alpha beta 1 = c * alpha + beta := by
  simp [splitAffineBlock, head2]

theorem splitAffineBlock_zero_one (c : K) :
    splitAffineBlock c 0 1 = splitDiagonalBlock := by
  funext j
  fin_cases j <;> simp [splitAffineBlock, splitDiagonalBlock, head2]

theorem splitAffineBlock_alpha_zero (c alpha : K) :
    splitAffineBlock c alpha 0 = isotropicLineBlock c alpha := by
  funext j
  fin_cases j <;> simp [splitAffineBlock, isotropicLineBlock, head2]

@[simp] theorem blockDefectLinear_splitAffineBlock
    (c alpha beta : K) :
    blockDefectLinear c (splitAffineBlock c alpha beta) = beta := by
  simp [blockDefectLinear, blockDefect, splitAffineBlock, head2]

@[simp] theorem blockDefectLinear_isotropicLineBlock
    (c alpha : K) :
    blockDefectLinear c (isotropicLineBlock c alpha) = 0 := by
  simp [blockDefectLinear, blockDefect, isotropicLineBlock, head2]

/-- The readout sends the boxed family to the block-diagonal coefficient
matrix `diag(I_k,D)`. -/
theorem rankBoxedReadout_rankBoxedRows {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K) :
    (rankBoxedReadout c H : RankBoxRow K k r →ₗ[K] _ ) ∘
        rankBoxedRows c P H Q A D = rankBoxedReadoutRows D := by
  funext x y
  cases x with
  | inl i =>
      cases y with
      | inl j => simp [rankBoxedReadout, rankBoxedRows, rankBoxedReadoutRows]
      | inr t => simp [rankBoxedReadout, rankBoxedRows, rankBoxedReadoutRows]
  | inr s =>
      cases y with
      | inl j => simp [rankBoxedReadout, rankBoxedRows, rankBoxedReadoutRows]
      | inr t =>
          simp [rankBoxedReadout, rankBoxedRows, rankBoxedReadoutRows]
          simp [isotropicLineBlock, head2]

/-- The block-diagonal readout family is linearly independent exactly from
the full-rank hypothesis on the free core. -/
theorem rankBoxedReadoutRows_linearIndependent {k r : ℕ}
    (D : Fin r → Fin r → K) (hD : RankBoxCoreFullRank D) :
    LinearIndependent K (rankBoxedReadoutRows (k := k) D) := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum x
  have hDli : LinearIndependent K (fun s => D s) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hD
  have hDsum : ∑ s, g (.inr s) • D s = 0 := by
    funext t
    have ht := congrFun hsum (.inr t)
    rw [Fintype.sum_sum_type] at ht
    simpa [rankBoxedReadoutRows, Pi.smul_apply, smul_eq_mul] using ht
  have hmaster : ∀ s, g (.inr s) = 0 :=
    (Fintype.linearIndependent_iff.mp hDli) _ hDsum
  cases x with
  | inl i =>
      have hi := congrFun hsum (.inl i)
      rw [Fintype.sum_sum_type] at hi
      simpa [rankBoxedReadoutRows, Pi.smul_apply, smul_eq_mul] using hi
  | inr s => exact hmaster s

/-- A full-rank free core makes all `k+r` rank-boxed generator rows linearly
independent, for arbitrary values of `P,H,Q,A`. -/
theorem rankBoxedRows_linearIndependent_of_core_fullRank {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K)
    (hD : RankBoxCoreFullRank D) :
    LinearIndependent K (rankBoxedRows c P H Q A D) := by
  apply LinearIndependent.of_comp (rankBoxedReadout c H)
  rw [rankBoxedReadout_rankBoxedRows]
  exact rankBoxedReadoutRows_linearIndependent D hD

/-- Once the pivot--master Gram relation is imposed, full rank of the free
core is also necessary for independence.  Thus `det D ≠ 0` is an exact
coordinate certificate, not an avoidable strengthening, inside the
orthogonal rank-boxed ansatz. -/
theorem rankBoxedRows_core_fullRank_of_linearIndependent {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K)
    (hpm : PivotMasterRelations Q A D)
    (hlin : LinearIndependent K (rankBoxedRows c P H Q A D)) :
    RankBoxCoreFullRank D := by
  rw [RankBoxCoreFullRank]
  intro hDzero
  obtain ⟨v, hvne, hvD⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hDzero
  have hvD' : ∀ t, ∑ s, v s * D s t = 0 := by
    intro t
    have ht := congrFun hvD t
    simpa [Matrix.vecMul, dotProduct] using ht
  have hvA : ∀ j, ∑ s, v s * A s j = 0 := by
    intro j
    calc
      ∑ s, v s * A s j =
          ∑ s, v s * (-(∑ t, Q j t * D s t)) := by
            apply Finset.sum_congr rfl
            intro s _
            rw [eq_neg_of_add_eq_zero_left (hpm s j)]
      _ = -(∑ t, Q j t * (∑ s, v s * D s t)) := by
            simp_rw [mul_neg]
            rw [Finset.sum_neg_distrib]
            congr 1
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro t _
            apply Finset.sum_congr rfl
            intro s _
            ring
      _ = 0 := by simp [hvD']
  let g : RankBoxIndex k r → K
    | .inl _ => 0
    | .inr s => v s
  have hsum : ∑ x, g x • rankBoxedRows c P H Q A D x = 0 := by
    funext x q
    rw [Fintype.sum_sum_type]
    simp only [g, zero_smul, Finset.sum_const_zero, zero_add]
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
    cases x with
    | inl j =>
        fin_cases q
        · simpa [rankBoxedRows, isotropicLineBlock, head2, Pi.smul_apply,
            smul_eq_mul] using hvA j
        · simp only [rankBoxedRows, isotropicLineBlock, head2, Pi.smul_apply,
            smul_eq_mul]
          calc
            ∑ x, v x * (c * A x j) = c * ∑ x, v x * A x j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              ring
            _ = 0 := by simp [hvA j]
    | inr t =>
        fin_cases q
        · simpa [rankBoxedRows, isotropicLineBlock, head2, Pi.smul_apply,
            smul_eq_mul] using hvD' t
        · simp only [rankBoxedRows, isotropicLineBlock, head2, Pi.smul_apply,
            smul_eq_mul]
          calc
            ∑ x, v x * (c * D x t) = c * ∑ x, v x * D x t := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              ring
            _ = 0 := by simp [hvD' t]
  have hgzero : ∀ x, g x = 0 :=
    (Fintype.linearIndependent_iff.mp hlin) g hsum
  apply hvne
  funext s
  exact hgzero (.inr s)

/-- Under the forced pivot--master relation, the determinant condition is
equivalent to the intrinsic independence condition on the whole generator
family. -/
theorem rankBoxedRows_linearIndependent_iff_core_fullRank {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K)
    (hpm : PivotMasterRelations Q A D) :
    LinearIndependent K (rankBoxedRows c P H Q A D) ↔
      RankBoxCoreFullRank D := by
  constructor
  · exact rankBoxedRows_core_fullRank_of_linearIndependent c P H Q A D hpm
  · exact rankBoxedRows_linearIndependent_of_core_fullRank c P H Q A D

theorem rankBoxRowInner_comm {k r : ℕ} (R S : RankBoxRow K k r) :
    rankBoxRowInner R S = rankBoxRowInner S R := by
  unfold rankBoxRowInner
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    exact dot_comm _ _
  · apply Finset.sum_congr rfl
    intro t _
    exact dot_comm _ _

@[simp] theorem rankBoxRowBilin_apply {k r : ℕ} (R S : RankBoxRow K k r) :
    rankBoxRowBilin R S = rankBoxRowInner R S := by
  rfl

theorem rankBoxRowBilin_isRefl {k r : ℕ} :
    (rankBoxRowBilin (K := K) (k := k) (r := r)).IsRefl := by
  intro R S hRS
  rw [rankBoxRowBilin_apply] at hRS ⊢
  rw [rankBoxRowInner_comm]
  exact hRS

theorem rankBoxRowBilin_separatingLeft {k r : ℕ} :
    LinearMap.SeparatingLeft (rankBoxRowBilin (K := K) (k := k) (r := r)) := by
  classical
  intro R hR
  funext x q
  cases x with
  | inl j =>
      have h := hR (Pi.single (.inl j) (Pi.single q (1 : K)))
      simp [rankBoxRowBilin, rankBoxRowInner, splitBlockInner, dot,
        Pi.single_apply] at h
      rw [Fintype.sum_eq_single j (fun x hx => by simp [hx])] at h
      fin_cases q <;>
        simpa [Pi.single_apply] using h
  | inr t =>
      have h := hR (Pi.single (.inr t) (Pi.single q (1 : K)))
      simp [rankBoxRowBilin, rankBoxRowInner, splitBlockInner, dot,
        Pi.single_apply] at h
      rw [Fintype.sum_eq_single t (fun x hx => by simp [hx])] at h
      fin_cases q <;>
        simpa [Pi.single_apply] using h

theorem rankBoxRowBilin_separatingRight {k r : ℕ} :
    LinearMap.SeparatingRight (rankBoxRowBilin (K := K) (k := k) (r := r)) := by
  intro R hR
  apply rankBoxRowBilin_separatingLeft
  intro S
  rw [rankBoxRowBilin_apply, rankBoxRowInner_comm]
  exact hR S

theorem rankBoxRowBilin_nondegenerate {k r : ℕ} :
    (rankBoxRowBilin (K := K) (k := k) (r := r)).Nondegenerate := by
  exact ⟨rankBoxRowBilin_separatingLeft, rankBoxRowBilin_separatingRight⟩

theorem rankBoxedRows_rowSpace_finrank_of_linearIndependent {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K)
    (hlin : LinearIndependent K (rankBoxedRows c P H Q A D)) :
    Module.finrank K ↥(rankBoxedRowSpace (rankBoxedRows c P H Q A D)) = k + r := by
  let e : ↥(rankBoxedRowSpace (rankBoxedRows c P H Q A D)) ≃ₗ[K]
      (RankBoxIndex k r →₀ K) :=
    LinearEquiv.ofBijective (hlin.repr)
      ⟨(LinearMap.ker_eq_bot.mp hlin.repr_ker),
        (LinearMap.range_eq_top.mp hlin.repr_range)⟩
  calc
    Module.finrank K ↥(rankBoxedRowSpace (rankBoxedRows c P H Q A D)) =
        Module.finrank K (RankBoxIndex k r →₀ K) := LinearEquiv.finrank_eq e
    _ = Fintype.card (RankBoxIndex k r) := by simp
    _ = k + r := by simp

theorem rankBoxedRowSpace_le_orthogonal {k r : ℕ}
    {R : RankBoxIndex k r → RankBoxRow K k r}
    (hR : RankBoxedPairwiseOrthogonal R) :
    rankBoxedRowSpace R ≤
      (rankBoxRowBilin (K := K) (k := k) (r := r)).orthogonal
        (rankBoxedRowSpace R) := by
  rw [rankBoxedRowSpace]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  apply (LinearMap.BilinForm.mem_orthogonal_iff).2
  intro w hw
  refine Submodule.span_induction
    (p := fun z _ =>
      (rankBoxRowBilin (K := K) (k := k) (r := r)).IsOrtho z (R i))
    ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨j, rfl⟩
    rw [LinearMap.BilinForm.isOrtho_def, rankBoxRowBilin_apply]
    exact hR j i
  · simpa using
      (LinearMap.BilinForm.isOrtho_zero_left
        (B := rankBoxRowBilin (K := K) (k := k) (r := r)) (x := R i))
  · intro x y hx hy hx0 hy0
    rw [LinearMap.BilinForm.isOrtho_def] at hx0 hy0 ⊢
    simp [hx0, hy0]
  · intro a x hx hx0
    rw [LinearMap.BilinForm.isOrtho_def] at hx0 ⊢
    simp [hx0]

/-- Orthogonality plus independence is the intrinsic forward self-duality
criterion.  No determinant presentation is needed at this layer. -/
theorem rankBoxedRows_rowSpace_selfDual {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K)
    (hlin : LinearIndependent K (rankBoxedRows c P H Q A D))
    (horth : RankBoxedPairwiseOrthogonal (rankBoxedRows c P H Q A D)) :
    rankBoxedRowSpace (rankBoxedRows c P H Q A D) =
      (rankBoxRowBilin (K := K) (k := k) (r := r)).orthogonal
        (rankBoxedRowSpace (rankBoxedRows c P H Q A D)) := by
  let C := rankBoxedRowSpace (rankBoxedRows c P H Q A D)
  let B := rankBoxRowBilin (K := K) (k := k) (r := r)
  have hle : C ≤ B.orthogonal C := rankBoxedRowSpace_le_orthogonal horth
  have hadd :
      Module.finrank K ↥C + Module.finrank K ↥(B.orthogonal C) =
        Module.finrank K (RankBoxRow K k r) +
          Module.finrank K ↥(C ⊓ B.orthogonal ⊤) := by
    simpa [B, C] using
      (LinearMap.BilinForm.finrank_add_finrank_orthogonal
        (B := B) (rankBoxRowBilin_isRefl (K := K) (k := k) (r := r)) C)
  have htop : B.orthogonal ⊤ = ⊥ := by
    rw [LinearMap.BilinForm.orthogonal_top_eq_ker
      (B := B) (rankBoxRowBilin_isRefl (K := K) (k := k) (r := r))]
    exact (rankBoxRowBilin_nondegenerate (K := K) (k := k) (r := r)).ker_eq_bot
  have hambient : Module.finrank K (RankBoxRow K k r) = 2 * (k + r) := by
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_fintype_fun_eq_card]
    omega
  have hdim : Module.finrank K ↥C = k + r := by
    exact rankBoxedRows_rowSpace_finrank_of_linearIndependent c P H Q A D hlin
  have hfinOrth : Module.finrank K ↥(B.orthogonal C) = k + r := by
    have hcalc := hadd
    rw [htop, inf_bot_eq] at hcalc
    simp [hambient] at hcalc
    omega
  apply Submodule.eq_of_le_of_finrank_eq hle
  exact hdim.trans hfinOrth.symm

/-- The Gram product of two affine split blocks before imposing
`c² = -1`. -/
theorem splitBlockInner_splitAffineBlock
    (c alpha beta alpha' beta' : K) :
    splitBlockInner (splitAffineBlock c alpha beta)
        (splitAffineBlock c alpha' beta') =
      (1 + c * c) * alpha * alpha' +
        c * (alpha * beta' + beta * alpha') + beta * beta' := by
  simp [splitBlockInner, splitAffineBlock, head2, dot]
  ring

/-- On the isotropic line `K(1,c)`, the affine-block Gram product depends
only on the transverse coefficients. -/
theorem splitBlockInner_splitAffineBlock_of_sq_neg_one
    (c alpha beta alpha' beta' : K) (hc : c * c = -1) :
    splitBlockInner (splitAffineBlock c alpha beta)
        (splitAffineBlock c alpha' beta') =
      c * (alpha * beta' + beta * alpha') + beta * beta' := by
  rw [splitBlockInner_splitAffineBlock, hc]
  ring

theorem splitBlockInner_splitAffine_isotropic
    (c alpha beta delta : K) (hc : c * c = -1) :
    splitBlockInner (splitAffineBlock c alpha beta)
        (isotropicLineBlock c delta) = c * beta * delta := by
  rw [← splitAffineBlock_alpha_zero]
  rw [splitBlockInner_splitAffineBlock_of_sq_neg_one _ _ _ _ _ hc]
  ring

theorem splitBlockInner_isotropic_splitAffine
    (c delta alpha beta : K) (hc : c * c = -1) :
    splitBlockInner (isotropicLineBlock c delta)
        (splitAffineBlock c alpha beta) = c * delta * beta := by
  rw [← splitAffineBlock_alpha_zero]
  rw [splitBlockInner_splitAffineBlock_of_sq_neg_one _ _ _ _ _ hc]
  ring

theorem splitBlockInner_isotropic_isotropic
    (c delta epsilon : K) (hc : c * c = -1) :
    splitBlockInner (isotropicLineBlock c delta)
        (isotropicLineBlock c epsilon) = 0 := by
  rw [← splitAffineBlock_alpha_zero, ← splitAffineBlock_alpha_zero]
  rw [splitBlockInner_splitAffineBlock_of_sq_neg_one _ _ _ _ _ hc]
  ring

/-- The pivot--pivot entry of the Gram matrix of `rankBoxedRows`. -/
theorem rankBoxRowInner_pivot_pivot {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K)
    (hc : c * c = -1) (i j : Fin k) :
    rankBoxRowInner (rankBoxedRows c P H Q A D (.inl i))
        (rankBoxedRows c P H Q A D (.inl j)) =
      (if i = j then 1 else 0) + c * (P i j + P j i) +
        ∑ t, (c * (H i t * Q j t + Q i t * H j t) +
          Q i t * Q j t) := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [rankBoxRowInner, rankBoxedRows]
    simp_rw [splitBlockInner_splitAffineBlock_of_sq_neg_one _ _ _ _ _ hc]
    simp only [mul_add, Finset.sum_add_distrib]
    simp
    ring
  · simp only [rankBoxRowInner, rankBoxedRows]
    simp_rw [splitBlockInner_splitAffineBlock_of_sq_neg_one _ _ _ _ _ hc]
    simp only [mul_add, Finset.sum_add_distrib]
    simp [hij]

/-- The pivot--master entry of the Gram matrix of `rankBoxedRows`. -/
theorem rankBoxRowInner_pivot_master {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K)
    (hc : c * c = -1) (i : Fin k) (s : Fin r) :
    rankBoxRowInner (rankBoxedRows c P H Q A D (.inl i))
        (rankBoxedRows c P H Q A D (.inr s)) =
      c * (A s i + ∑ t, Q i t * D s t) := by
  simp only [rankBoxRowInner, rankBoxedRows]
  simp_rw [splitBlockInner_splitAffine_isotropic _ _ _ _ hc]
  rw [mul_add, Finset.mul_sum]
  simp [mul_assoc]

/-- The master--pivot entry, included explicitly so that the formal Gram
matrix is symmetric without an implicit appeal to dot-product symmetry. -/
theorem rankBoxRowInner_master_pivot {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K)
    (hc : c * c = -1) (s : Fin r) (i : Fin k) :
    rankBoxRowInner (rankBoxedRows c P H Q A D (.inr s))
        (rankBoxedRows c P H Q A D (.inl i)) =
      c * (A s i + ∑ t, Q i t * D s t) := by
  rw [rankBoxRowInner_comm]
  exact rankBoxRowInner_pivot_master c P H Q A D hc i s

/-- Master rows lie entirely on the isotropic line, hence have zero mutual
Gram product independently of the entries of the free core `D`. -/
theorem rankBoxRowInner_master_master {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K)
    (hc : c * c = -1) (s u : Fin r) :
    rankBoxRowInner (rankBoxedRows c P H Q A D (.inr s))
        (rankBoxedRows c P H Q A D (.inr u)) = 0 := by
  simp only [rankBoxRowInner, rankBoxedRows]
  simp_rw [splitBlockInner_isotropic_isotropic _ _ _ hc]
  simp

/-- The two displayed matrix relations are sufficient for pairwise
orthogonality of the rank-boxed construction.  Full rank of `D`
is intentionally absent here: it is the independent rank condition used to
obtain a self-dual generator matrix, not an orthogonality condition. -/
theorem rankBoxedRows_pairwiseOrthogonal {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K)
    (hc : c * c = -1)
    (hpm : PivotMasterRelations Q A D)
    (hpp : PivotGramRelations c P H Q) :
    RankBoxedPairwiseOrthogonal (rankBoxedRows c P H Q A D) := by
  intro x y
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          rw [rankBoxRowInner_pivot_pivot c P H Q A D hc i j]
          exact hpp i j
      | inr s =>
          rw [rankBoxRowInner_pivot_master c P H Q A D hc i s, hpm s i,
            mul_zero]
  | inr s =>
      cases y with
      | inl i =>
          rw [rankBoxRowInner_master_pivot c P H Q A D hc s i, hpm s i,
            mul_zero]
      | inr u =>
          exact rankBoxRowInner_master_master c P H Q A D hc s u

/-- Minimal intrinsic forward theorem: the matrix relations give
orthogonality, while independence is stated directly rather than through a
chosen determinant certificate. -/
theorem rankBoxedRows_forward_selfDual_of_linearIndependent {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K)
    (hc : c * c = -1)
    (hlin : LinearIndependent K (rankBoxedRows c P H Q A D))
    (hpm : PivotMasterRelations Q A D)
    (hpp : PivotGramRelations c P H Q) :
    RankBoxedPairwiseOrthogonal (rankBoxedRows c P H Q A D) ∧
      LinearIndependent K (rankBoxedRows c P H Q A D) ∧
      rankBoxedRowSpace (rankBoxedRows c P H Q A D) =
        (rankBoxRowBilin (K := K) (k := k) (r := r)).orthogonal
          (rankBoxedRowSpace (rankBoxedRows c P H Q A D)) := by
  have horth := rankBoxedRows_pairwiseOrthogonal c P H Q A D hc hpm hpp
  exact ⟨horth, hlin,
    rankBoxedRows_rowSpace_selfDual c P H Q A D hlin horth⟩

/-- Concrete determinant-certified form of the forward theorem.  The
determinant is not part of the self-duality argument; it is a convenient
certificate for the intrinsic independence hypothesis above. -/
theorem rankBoxedRows_forward_selfDual {k r : ℕ}
    (c : K)
    (P : Fin k → Fin k → K)
    (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K)
    (D : Fin r → Fin r → K)
    (hc : c * c = -1)
    (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D)
    (hpp : PivotGramRelations c P H Q) :
    RankBoxedPairwiseOrthogonal (rankBoxedRows c P H Q A D) ∧
      LinearIndependent K (rankBoxedRows c P H Q A D) ∧
      rankBoxedRowSpace (rankBoxedRows c P H Q A D) =
        (rankBoxRowBilin (K := K) (k := k) (r := r)).orthogonal
          (rankBoxedRowSpace (rankBoxedRows c P H Q A D)) := by
  exact rankBoxedRows_forward_selfDual_of_linearIndependent c P H Q A D hc
    (rankBoxedRows_linearIndependent_of_core_fullRank c P H Q A D hD) hpm hpp

theorem binaryCzRankOneRows_pivot_diagonal [CharP K 2]
    {k : ℕ} (b : Fin k → Fin k → K) (i : Fin k) (hdiag : b i i = 0) :
    binaryCzRankOneRows b (.inl i) (.inl i) = splitDiagonalBlock := by
  simp [binaryCzRankOneRows, rankBoxedRows, hdiag, splitAffineBlock_zero_one]

theorem binaryCzRankOneRows_pivot_offDiagonal [CharP K 2]
    {k : ℕ} (b : Fin k → Fin k → K) {i j : Fin k} (hij : i ≠ j) :
    binaryCzRankOneRows b (.inl i) (.inl j) =
      isotropicLineBlock 1 (b i j) := by
  simp [binaryCzRankOneRows, rankBoxedRows, hij, splitAffineBlock_alpha_zero]

theorem binaryCzRankOneRows_pivot_terminal [CharP K 2]
    {k : ℕ} (b : Fin k → Fin k → K) (i : Fin k) (t : Fin 1) :
    binaryCzRankOneRows b (.inl i) (.inr t) = head2 1 0 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hone : (1 : K) + 1 = 0 := by
    simpa [one_add_one_eq_two] using htwo
  funext j
  fin_cases j <;>
    simp [binaryCzRankOneRows, rankBoxedRows, splitAffineBlock, head2, hone]

theorem binaryCzRankOneRows_master_pivot [CharP K 2]
    {k : ℕ} (b : Fin k → Fin k → K) (s : Fin 1) (j : Fin k) :
    binaryCzRankOneRows b (.inr s) (.inl j) = head2 1 1 := by
  funext q
  fin_cases q <;>
    simp [binaryCzRankOneRows, rankBoxedRows, isotropicLineBlock, head2]

theorem binaryCzRankOneRows_master_terminal [CharP K 2]
    {k : ℕ} (b : Fin k → Fin k → K) (s t : Fin 1) :
    binaryCzRankOneRows b (.inr s) (.inr t) = head2 1 1 := by
  funext q
  fin_cases q <;>
    simp [binaryCzRankOneRows, rankBoxedRows, isotropicLineBlock, head2]

/-- Literal blockwise identification with the Chinburg--Zhang binary box:
diagonal `01`, off-diagonal `b_ij(11)`, terminal `10`, and master `11`. -/
theorem binaryCzRankOneRows_exact_block_form [CharP K 2]
    {k : ℕ} (b : Fin k → Fin k → K) (hdiag : ∀ i, b i i = 0) :
    (∀ i, binaryCzRankOneRows b (.inl i) (.inl i) = splitDiagonalBlock) ∧
    (∀ i j, i ≠ j → binaryCzRankOneRows b (.inl i) (.inl j) =
      isotropicLineBlock 1 (b i j)) ∧
    (∀ i t, binaryCzRankOneRows b (.inl i) (.inr t) = head2 1 0) ∧
    (∀ s j, binaryCzRankOneRows b (.inr s) (.inl j) = head2 1 1) ∧
    (∀ s t, binaryCzRankOneRows b (.inr s) (.inr t) = head2 1 1) := by
  refine ⟨fun i => binaryCzRankOneRows_pivot_diagonal b i (hdiag i), ?_⟩
  refine ⟨fun i j hij => binaryCzRankOneRows_pivot_offDiagonal b hij, ?_⟩
  refine ⟨binaryCzRankOneRows_pivot_terminal b, ?_⟩
  exact ⟨binaryCzRankOneRows_master_pivot b,
    binaryCzRankOneRows_master_terminal b⟩

/-- In characteristic two the rank-one specialization satisfies exactly the
Chinburg--Zhang opposite-block rule from Theorem 3.4.  Consequently the
literal block form proved above is pairwise orthogonal. -/
theorem binaryCzRankOneRows_pairwiseOrthogonal [CharP K 2]
    {k : ℕ} (b : Fin k → Fin k → K)
    (hdiag : ∀ i, b i i = 0)
    (hopposite : ∀ i j, i ≠ j → b i j + b j i = 1) :
    RankBoxedPairwiseOrthogonal (binaryCzRankOneRows b) := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hone : (1 : K) + 1 = 0 := by
    simpa [one_add_one_eq_two] using htwo
  have hc : (1 : K) * 1 = -1 := by
    rw [one_mul]
    exact eq_neg_of_add_eq_zero_left hone
  have hpm : PivotMasterRelations
      (fun (_ : Fin k) (_ : Fin 1) => (1 : K))
      (fun (_ : Fin 1) (_ : Fin k) => (1 : K))
      (fun (_ : Fin 1) (_ : Fin 1) => (1 : K)) := by
    intro s i
    simp [hone]
  have hpp : PivotGramRelations (1 : K) b
      (fun (_ : Fin k) (_ : Fin 1) => (1 : K))
      (fun (_ : Fin k) (_ : Fin 1) => (1 : K)) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [hdiag, hone]
    · simp [hij, hopposite i j hij, hone]
  exact rankBoxedRows_pairwiseOrthogonal (1 : K) b
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1)
    hc hpm hpp

/-- For a one-dimensional master block, the full-rank condition is exactly
nonvanishing of its single scalar.  This statement is field-independent. -/
theorem rankOne_core_fullRank_iff (d : K) :
    RankBoxCoreFullRank
        (fun (_ : Fin 1) (_ : Fin 1) => d) ↔ d ≠ 0 := by
  rw [RankBoxCoreFullRank, Matrix.det_fin_one]

/-- A unit-normalized rank-one core is automatically full rank over every
field, not only in characteristic two. -/
theorem rankOne_unit_core_fullRank :
    RankBoxCoreFullRank
      (fun (_ : Fin 1) (_ : Fin 1) => (1 : K)) := by
  exact (rankOne_core_fullRank_iff (1 : K)).2 one_ne_zero

/-- The Theorem 3.4 binary box has already chosen the unit normalization, so
its determinant hypothesis is present but automatic. -/
theorem binaryCzRankOne_core_fullRank :
    RankBoxCoreFullRank
      (fun (_ : Fin 1) (_ : Fin 1) => (1 : K)) :=
  rankOne_unit_core_fullRank

end BuildingUpFormalization.Components.RankBoxed
