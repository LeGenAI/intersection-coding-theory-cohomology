import Formalization.Components.QaryRankBoxedNormalizationDefinitions
import Formalization.Components.RankBoxedConstruction
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

set_option autoImplicit false

noncomputable section

namespace BuildingUpFormalization.Components.QaryRankBoxedNormalization

open Set
open Module
open BuildingUpFormalization.Components.SplitBoxed
open BuildingUpFormalization.Components.RankBoxed

variable {K : Type*} [Field K]

@[simp] theorem qaryBlockBilin_apply {ι : Type*} [Fintype ι]
    (R S : QaryBlockRow K ι) :
    qaryBlockBilin R S = qaryBlockInner R S := rfl

theorem qaryBlockInner_comm {ι : Type*} [Fintype ι]
    (R S : QaryBlockRow K ι) :
    qaryBlockInner R S = qaryBlockInner S R := by
  unfold qaryBlockInner
  apply Finset.sum_congr rfl
  intro i _
  exact dot_comm _ _

/-- Relabelling whole two-coordinate blocks preserves the Euclidean inner
product exactly. -/
theorem qaryBlockInner_blockRelabel {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (σ : ι ≃ κ) (R S : QaryBlockRow K κ) :
    qaryBlockInner
        (blockRelabelLinearEquiv (K := K) σ R)
        (blockRelabelLinearEquiv (K := K) σ S) =
      qaryBlockInner R S := by
  unfold qaryBlockInner blockRelabelLinearEquiv
  exact Fintype.sum_equiv σ _ _ (fun _ => rfl)

/-- The rank-box inner product is the same Euclidean block product, merely
written with the pivot/master sum split in two. -/
theorem rankBoxRowInner_eq_qaryBlockInner {k r : ℕ}
    (R S : RankBoxRow K k r) :
    rankBoxRowInner R S = qaryBlockInner R S := by
  unfold rankBoxRowInner qaryBlockInner
  rw [Fintype.sum_sum_type]

theorem qaryBlockBilin_isRefl {ι : Type*} [Fintype ι] :
    (qaryBlockBilin (K := K) (ι := ι)).IsRefl := by
  intro R S h
  rw [qaryBlockBilin_apply] at h ⊢
  rw [qaryBlockInner_comm]
  exact h

theorem qaryBlockBilin_separatingLeft {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    LinearMap.SeparatingLeft (qaryBlockBilin (K := K) (ι := ι)) := by
  intro R hR
  funext i q
  have h := hR (Pi.single i (Pi.single q (1 : K)))
  simp [qaryBlockBilin, qaryBlockInner, splitBlockInner, dot,
    Pi.single_apply] at h
  rw [Fintype.sum_eq_single i (fun x hx => by simp [hx])] at h
  fin_cases q <;> simpa [Pi.single_apply] using h

theorem qaryBlockBilin_nondegenerate {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    (qaryBlockBilin (K := K) (ι := ι)).Nondegenerate := by
  refine ⟨qaryBlockBilin_separatingLeft (K := K) (ι := ι), ?_⟩
  intro R hR
  apply qaryBlockBilin_separatingLeft
  intro S
  rw [qaryBlockBilin_apply, qaryBlockInner_comm]
  exact hR S

theorem qaryBlockSelfDualCode_finrank {n : ℕ}
    {C : Submodule K (QaryBlockRow K (Fin n))}
    (hC : QaryBlockSelfDualCode C) :
    Module.finrank K C = n := by
  let B := qaryBlockBilin (K := K) (ι := Fin n)
  have horth :
      Module.finrank K (B.orthogonal C) =
        Module.finrank K (QaryBlockRow K (Fin n)) -
          Module.finrank K C :=
    LinearMap.BilinForm.finrank_orthogonal
      (qaryBlockBilin_nondegenerate (K := K) (ι := Fin n)) C
  have hambient :
      Module.finrank K (QaryBlockRow K (Fin n)) = 2 * n := by
    rw [Module.finrank_pi_fintype]
    simpa [SplitBlock, Module.finrank_fintype_fun_eq_card, mul_comm]
  have heq :
      Module.finrank K C =
        Module.finrank K (B.orthogonal C) := by
    unfold QaryBlockSelfDualCode at hC
    simpa [B] using congrArg
      (fun S : Submodule K (QaryBlockRow K (Fin n)) =>
        Module.finrank K S) hC
  rw [hambient] at horth
  omega

/-- Every block is recovered from its first coordinate and defect. -/
theorem splitAffineBlock_first_defect (c : K) (v : SplitBlock K) :
    splitAffineBlock c (v 0) (blockDefectLinear c v) = v := by
  funext q
  fin_cases q <;>
    simp [splitAffineBlock, blockDefectLinear, blockDefect, head2]

/-- The intersection defining the intrinsic master rank is the kernel of the
defect map restricted to the code. -/
theorem map_ker_restrict_eq_inf_isotropicLineCode {n : ℕ}
    (c : K) (C : Submodule K (QaryBlockRow K (Fin n))) :
    Submodule.map C.subtype
        (LinearMap.ker
          ((qaryBlockDefectLinear (K := K) (ι := Fin n) c).comp C.subtype)) =
      C ⊓ qaryIsotropicLineCode (K := K) c := by
  ext v
  simp [qaryIsotropicLineCode, and_comm]

/-- Restriction of an ambient coordinate functional to a subspace. -/
def coordinateDual {n : ℕ} (W : Submodule K (Fin n → K)) (j : Fin n) :
    Module.Dual K W where
  toFun w := (w : Fin n → K) j
  map_add' u v := rfl
  map_smul' a v := rfl

theorem coordinateDual_span_eq_top {n : ℕ}
    (W : Submodule K (Fin n → K)) :
    Submodule.span K (Set.range (coordinateDual (K := K) W)) = ⊤ := by
  apply Submodule.span_eq_top_of_ne_zero
  intro w hw
  have hex : ∃ j : Fin n, (w : Fin n → K) j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hw
    apply Subtype.ext
    funext j
    exact h j
  obtain ⟨j, hj⟩ := hex
  exact ⟨coordinateDual W j, ⟨j, rfl⟩, hj⟩

theorem basis_coe_submodule_linearIndependent
    {M ι : Type*} [AddCommGroup M] [Module K M]
    (p : Submodule K M) (b : Basis ι K p) :
    LinearIndependent K (fun i => (b i : M)) := by
  exact b.linearIndependent.map' p.subtype (Submodule.ker_subtype p)

/-- A basis of a coordinate subspace together with pivot coordinates and
their complementary block coordinates. -/
structure CoordinatePivotBasisData {n : ℕ}
    (W : Submodule K (Fin n → K)) where
  k : ℕ
  r : ℕ
  k_add_r : k + r = n
  k_eq_finrank : k = Module.finrank K W
  sigma : RankBoxIndex k r ≃ Fin n
  basis : Basis (Fin k) K W
  apply_pivot : ∀ i j,
    ((basis i : W) : Fin n → K) (sigma (.inl j)) =
      if i = j then 1 else 0

/-- Gaussian pivot selection expressed without an arbitrary ambient change of
basis: the selected pivot functionals are restrictions of literal
coordinates, so `sigma` is a block-coordinate permutation. -/
theorem exists_coordinatePivotBasisData {n : ℕ}
    (W : Submodule K (Fin n → K)) :
    Nonempty (CoordinatePivotBasisData W) := by
  let Sdual : Set (Module.Dual K W) :=
    Set.range (coordinateDual (K := K) W)
  obtain ⟨f₀, hf₀_mem, hf₀_span, hf₀_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K Sdual
  have hspan : Submodule.span K Sdual = ⊤ :=
    coordinateDual_span_eq_top W
  have hdim :
      Module.finrank K (Submodule.span K Sdual) =
        Module.finrank K W := by
    rw [hspan, finrank_top, Subspace.dual_finrank_eq]
  let k := Module.finrank K W
  let eidx : Fin k ≃ Fin (Module.finrank K (Submodule.span K Sdual)) :=
    finCongr hdim.symm
  let f : Fin k → Module.Dual K W := fun i => f₀ (eidx i)
  have hf_mem : ∀ i, f i ∈ Sdual := fun i => hf₀_mem (eidx i)
  have hf_li : LinearIndependent K f :=
    hf₀_li.comp eidx eidx.injective
  have hf_span : Submodule.span K (Set.range f) = ⊤ := by
    have hrange : Set.range f = Set.range f₀ := by
      apply Set.Subset.antisymm
      · rintro _ ⟨i, rfl⟩
        exact ⟨eidx i, rfl⟩
      · rintro _ ⟨i, rfl⟩
        exact ⟨eidx.symm i, by simp [f]⟩
    rw [hrange, hf₀_span, hspan]
  let bDual : Basis (Fin k) K (Module.Dual K W) :=
    Basis.mk hf_li hf_span.ge
  let bW : Basis (Fin k) K W :=
    bDual.dualBasis.map (Module.evalEquiv K W).symm
  choose pivot hpivot using hf_mem
  have hpivot_eq : ∀ i, f i = coordinateDual W (pivot i) := by
    intro i
    exact (hpivot i).symm
  have hpivot_inj : Function.Injective pivot := by
    intro i j hij
    apply hf_li.injective
    rw [hpivot_eq i, hpivot_eq j, hij]
  let pivotEmb : Fin k ↪ Fin n := ⟨pivot, hpivot_inj⟩
  let T : Set (Fin n) := Set.range pivot
  let epivot : Fin k ≃ T := pivotEmb.toEquivRange
  let r := Fintype.card (Tᶜ : Set (Fin n))
  let erest : Fin r ≃ (Tᶜ : Set (Fin n)) :=
    (Fintype.equivFin (Tᶜ : Set (Fin n))).symm
  let sigma : RankBoxIndex k r ≃ Fin n :=
    (Equiv.sumCongr epivot erest).trans (Equiv.Set.sumCompl T)
  have hk_add_r : k + r = n := by
    simpa [RankBoxIndex] using Fintype.card_congr sigma
  have hsigma_pivot : ∀ j, sigma (.inl j) = pivot j := by
    intro j
    rfl
  refine ⟨{
    k := k
    r := r
    k_add_r := hk_add_r
    k_eq_finrank := rfl
    sigma := sigma
    basis := bW
    apply_pivot := ?_
  }⟩
  intro i j
  rw [hsigma_pivot]
  change coordinateDual W (pivot j) (bW i) = _
  rw [← hpivot_eq j]
  have hbDual : bDual j = f j := by
    simp [bDual]
  have hbW :
      bW i = (Module.evalEquiv K W).symm (bDual.dualBasis i) := by
    simp [bW]
  rw [← hbDual, hbW]
  rw [Module.apply_evalEquiv_symm_apply,
    Basis.dualBasis_apply_self]
  simp [eq_comm]

set_option maxHeartbeats 800000 in
theorem every_qary_selfDualCode_has_rankBoxed_normalForm
    {n : ℕ} (c : K) (hc : c ^ 2 = (-1 : K))
    (h2 : (2 : K) ≠ 0)
    {C : Submodule K (QaryBlockRow K (Fin n))}
    (hC : QaryBlockSelfDualCode C) :
    HasQaryRankBoxedNormalForm c C := by
  let beta : C →ₗ[K] (Fin n → K) :=
    (qaryBlockDefectLinear (K := K) (ι := Fin n) c).comp C.subtype
  let W := LinearMap.range beta
  let data : CoordinatePivotBasisData W :=
    Classical.choice (exists_coordinatePivotBasisData W)
  let k := data.k
  let r := data.r
  have hCdim : Module.finrank K C = n :=
    qaryBlockSelfDualCode_finrank hC
  have hnull := LinearMap.finrank_range_add_finrank_ker beta
  have hkerdim : Module.finrank K (LinearMap.ker beta) = r := by
    change Module.finrank K W +
      Module.finrank K (LinearMap.ker beta) = Module.finrank K C at hnull
    rw [← data.k_eq_finrank, hCdim] at hnull
    have hkr := data.k_add_r
    omega
  have hr_intrinsic :
      r = Module.finrank K
        ↥(C ⊓ qaryIsotropicLineCode (K := K) c) := by
    calc
      r = Module.finrank K (LinearMap.ker beta) := hkerdim.symm
      _ = Module.finrank K
          (Submodule.map C.subtype (LinearMap.ker beta)) := by
            symm
            exact Submodule.finrank_map_subtype_eq C (LinearMap.ker beta)
      _ = Module.finrank K
          ↥(C ⊓ qaryIsotropicLineCode (K := K) c) := by
            have hmap :
                Submodule.map C.subtype (LinearMap.ker beta) =
                  C ⊓ qaryIsotropicLineCode (K := K) c := by
              simpa [beta] using
                map_ker_restrict_eq_inf_isotropicLineCode c C
            rw [hmap]
  choose pivotRows hpivotRows using
    fun i : Fin k => (data.basis i).property
  have hpivotRows_beta :
      ∀ i : Fin k, beta (pivotRows i) = data.basis i := by
    intro i
    exact hpivotRows i
  let bker₀ : Basis
      (Module.Basis.ofVectorSpaceIndex K (LinearMap.ker beta))
      K (LinearMap.ker beta) :=
    Module.Basis.ofVectorSpace K (LinearMap.ker beta)
  letI : Fintype
      (Module.Basis.ofVectorSpaceIndex K (LinearMap.ker beta)) :=
    Fintype.ofFinite _
  have hker_card :
      Fintype.card
          (Module.Basis.ofVectorSpaceIndex K (LinearMap.ker beta)) = r := by
    calc
      Fintype.card
          (Module.Basis.ofVectorSpaceIndex K (LinearMap.ker beta)) =
          Module.finrank K (LinearMap.ker beta) :=
            (Module.finrank_eq_card_basis bker₀).symm
      _ = r := hkerdim
  let eker :
      Module.Basis.ofVectorSpaceIndex K (LinearMap.ker beta) ≃ Fin r :=
    Fintype.equivFinOfCardEq hker_card
  let bker : Basis (Fin r) K (LinearMap.ker beta) :=
    bker₀.reindex eker
  let masterRows : Fin r → C := fun s => (bker s : LinearMap.ker beta)
  have hmaster_beta : ∀ s, beta (masterRows s) = 0 := by
    intro s
    exact (bker s).property
  let baseRows : RankBoxIndex k r → C
    | .inl i => pivotRows i
    | .inr s => masterRows s
  have hbase_li : LinearIndependent K baseRows := by
    rw [Fintype.linearIndependent_iff]
    intro g hsum x
    have hsum_beta := congrArg beta hsum
    rw [map_zero, map_sum] at hsum_beta
    rw [Fintype.sum_sum_type] at hsum_beta
    simp only [baseRows, map_smul, hpivotRows_beta, hmaster_beta,
      smul_zero, Finset.sum_const_zero, add_zero] at hsum_beta
    have hbasis_ambient :
        LinearIndependent K
          (fun i => ((data.basis i : W) : Fin n → K)) :=
      basis_coe_submodule_linearIndependent W data.basis
    have hpivot_zero : ∀ i, g (.inl i) = 0 :=
      (Fintype.linearIndependent_iff.mp hbasis_ambient)
        (fun i => g (.inl i)) hsum_beta
    cases x with
    | inl i => exact hpivot_zero i
    | inr s =>
        rw [Fintype.sum_sum_type] at hsum
        simp only [baseRows, hpivot_zero, zero_smul,
          Finset.sum_const_zero, zero_add] at hsum
        have hmaster_li : LinearIndependent K masterRows := by
          simpa [masterRows] using
            basis_coe_submodule_linearIndependent
              (LinearMap.ker beta) bker
        exact (Fintype.linearIndependent_iff.mp hmaster_li)
          (fun t => g (.inr t)) hsum s
  have hbase_card :
      Fintype.card (RankBoxIndex k r) = Module.finrank K C := by
    calc
      Fintype.card (RankBoxIndex k r) = k + r := by simp [RankBoxIndex]
      _ = n := data.k_add_r
      _ = Module.finrank K C := hCdim.symm
  have hbase_span :
      Submodule.span K (Set.range baseRows) = ⊤ :=
    hbase_li.span_eq_top_of_card_eq_finrank' hbase_card
  let L : QaryBlockRow K (Fin n) ≃ₗ[K] RankBoxRow K k r :=
    blockRelabelLinearEquiv (K := K) data.sigma
  let rows : RankBoxIndex k r → RankBoxRow K k r :=
    fun x => L (baseRows x)
  have hpivot_defect : ∀ i j,
      blockDefectLinear c (rows (.inl i) (.inl j)) =
        if i = j then 1 else 0 := by
    intro i j
    have h := congrFun (hpivotRows_beta i) (data.sigma (.inl j))
    change blockDefectLinear c
      (((pivotRows i : C) : QaryBlockRow K (Fin n))
        (data.sigma (.inl j))) =
      ((data.basis i : W) : Fin n → K) (data.sigma (.inl j)) at h
    change blockDefectLinear c
      (((pivotRows i : C) : QaryBlockRow K (Fin n))
        (data.sigma (.inl j))) =
      if i = j then 1 else 0
    exact h.trans (data.apply_pivot i j)
  have hmaster_defect : ∀ s y,
      blockDefectLinear c (rows (.inr s) y) = 0 := by
    intro s y
    have h := congrFun (hmaster_beta s) (data.sigma y)
    change blockDefectLinear c
      (((masterRows s : C) : QaryBlockRow K (Fin n))
        (data.sigma y)) = 0 at h
    change blockDefectLinear c
      (((masterRows s : C) : QaryBlockRow K (Fin n))
        (data.sigma y)) = 0
    exact h
  let P : Fin k → Fin k → K :=
    fun i j => rows (.inl i) (.inl j) 0
  let H : Fin k → Fin r → K :=
    fun i t => rows (.inl i) (.inr t) 0
  let Q : Fin k → Fin r → K :=
    fun i t => blockDefectLinear c (rows (.inl i) (.inr t))
  let A : Fin r → Fin k → K :=
    fun s j => rows (.inr s) (.inl j) 0
  let D : Fin r → Fin r → K :=
    fun s t => rows (.inr s) (.inr t) 0
  have hrows_boxed :
      rows = rankBoxedRows c P H Q A D := by
    funext x y
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            change rows (.inl i) (.inl j) =
              splitAffineBlock c (P i j)
                (if i = j then 1 else 0)
            symm
            rw [← hpivot_defect i j]
            exact splitAffineBlock_first_defect c
              (rows (.inl i) (.inl j))
        | inr t =>
            change rows (.inl i) (.inr t) =
              splitAffineBlock c (H i t) (Q i t)
            symm
            exact splitAffineBlock_first_defect c
              (rows (.inl i) (.inr t))
    | inr s =>
        cases y with
        | inl j =>
            change rows (.inr s) (.inl j) =
              isotropicLineBlock c (A s j)
            rw [← splitAffineBlock_alpha_zero]
            symm
            rw [← hmaster_defect s (.inl j)]
            exact splitAffineBlock_first_defect c
              (rows (.inr s) (.inl j))
        | inr t =>
            change rows (.inr s) (.inr t) =
              isotropicLineBlock c (D s t)
            rw [← splitAffineBlock_alpha_zero]
            symm
            rw [← hmaster_defect s (.inr t)]
            exact splitAffineBlock_first_defect c
              (rows (.inr s) (.inr t))
  have hL_injective :
      Function.Injective (L.toLinearMap.comp C.subtype) :=
    L.injective.comp C.injective_subtype
  have hrows_li : LinearIndependent K rows := by
    have hmap := hbase_li.map' (L.toLinearMap.comp C.subtype)
      (LinearMap.ker_eq_bot.mpr hL_injective)
    simpa [rows, Function.comp_def] using hmap
  let B := qaryBlockBilin (K := K) (ι := Fin n)
  have hCeq : C = B.orthogonal C := by
    simpa [B, QaryBlockSelfDualCode] using hC
  have hbase_inner : ∀ x y,
      qaryBlockInner
          (((baseRows x : C) : QaryBlockRow K (Fin n)))
          (((baseRows y : C) : QaryBlockRow K (Fin n))) = 0 := by
    intro x y
    have hxorth :
        (((baseRows x : C) : QaryBlockRow K (Fin n))) ∈
          B.orthogonal C := by
      rw [← hCeq]
      exact (baseRows x).property
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hxorth)
      (((baseRows y : C) : QaryBlockRow K (Fin n)))
      (baseRows y).property
    change qaryBlockInner
        (((baseRows y : C) : QaryBlockRow K (Fin n)))
        (((baseRows x : C) : QaryBlockRow K (Fin n))) = 0 at h
    rw [qaryBlockInner_comm] at h
    exact h
  have hrows_orth : RankBoxedPairwiseOrthogonal rows := by
    intro x y
    rw [rankBoxRowInner_eq_qaryBlockInner]
    change qaryBlockInner
        (blockRelabelLinearEquiv (K := K) data.sigma
          (((baseRows x : C) : QaryBlockRow K (Fin n))))
        (blockRelabelLinearEquiv (K := K) data.sigma
          (((baseRows y : C) : QaryBlockRow K (Fin n)))) = 0
    rw [qaryBlockInner_blockRelabel]
    exact hbase_inner x y
  have hboxed_li :
      LinearIndependent K (rankBoxedRows c P H Q A D) := by
    rw [← hrows_boxed]
    exact hrows_li
  have hboxed_orth :
      RankBoxedPairwiseOrthogonal (rankBoxedRows c P H Q A D) := by
    rw [← hrows_boxed]
    exact hrows_orth
  have hc_mul : c * c = (-1 : K) := by
    simpa [pow_two] using hc
  have hc_ne : c ≠ 0 := by
    intro hc_zero
    subst c
    simp at hc
  have hpm : PivotMasterRelations Q A D := by
    intro s i
    have h := hboxed_orth (.inl i) (.inr s)
    rw [rankBoxRowInner_pivot_master c P H Q A D hc_mul i s] at h
    exact (mul_eq_zero.mp h).resolve_left hc_ne
  have hpp : PivotGramRelations c P H Q := by
    intro i j
    have h := hboxed_orth (.inl i) (.inl j)
    rw [rankBoxRowInner_pivot_pivot c P H Q A D hc_mul i j] at h
    exact h
  have hD : RankBoxCoreFullRank D :=
    rankBoxedRows_core_fullRank_of_linearIndependent
      c P H Q A D hpm hboxed_li
  have hrowSpace_le :
      rankBoxedRowSpace rows ≤ relabelBlockCode (K := K) data.sigma C := by
    rw [rankBoxedRowSpace, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨baseRows x, (baseRows x).property, rfl⟩
  have hrowSpace_finrank :
      Module.finrank K (rankBoxedRowSpace rows) = k + r := by
    rw [hrows_boxed]
    exact rankBoxedRows_rowSpace_finrank_of_linearIndependent
      c P H Q A D hboxed_li
  have hrelabel_finrank :
      Module.finrank K (relabelBlockCode (K := K) data.sigma C) = n := by
    unfold relabelBlockCode
    rw [L.finrank_map_eq]
    exact hCdim
  have hrowSpace_eq :
      rankBoxedRowSpace rows =
        relabelBlockCode (K := K) data.sigma C := by
    apply Submodule.eq_of_le_of_finrank_eq hrowSpace_le
    rw [hrowSpace_finrank, hrelabel_finrank, data.k_add_r]
  have hcode_eq :
      relabelBlockCode (K := K) data.sigma C =
        rankBoxedRowSpace (rankBoxedRows c P H Q A D) := by
    rw [← hrows_boxed, hrowSpace_eq]
  have hA : A = forcedMasterCoefficients Q D := by
    funext s i
    change A s i = -(∑ t, Q i t * D s t)
    exact eq_neg_of_add_eq_zero_left (hpm s i)
  have hcode_determined :
      relabelBlockCode (K := K) data.sigma C =
        rankBoxedRowSpace (determinedRankBoxedRows c P H Q D) := by
    simpa [determinedRankBoxedRows, hA] using hcode_eq
  let ell : Fin k → Fin r → SplitBlock K :=
    fun i t => splitAffineBlock c (H i t) (Q i t)
  let b : Fin k → Fin k → K := P
  have hellFirst : terminalFirst ell = H := by
    funext i t
    simp [ell, terminalFirst, splitAffineBlock, head2]
  have hellDefect : terminalDefect c ell = Q := by
    funext i t
    simp [ell, terminalDefect]
  have hterminal (i j : Fin k) :
      terminalInner ell i j =
        ∑ t, (c * (H i t * Q j t + Q i t * H j t) +
          Q i t * Q j t) := by
    rw [← terminalInner_identity c ell hc_mul i j, hellFirst, hellDefect]
  have hoff : PaperOffDiagonalRelations c b ell := by
    intro i j hij
    have h := hpp i j
    simp only [if_neg hij] at h
    rw [hterminal i j]
    simpa only [zero_add, b] using h
  have hdiag (i : Fin k) :
      P i i = forcedPivotDiagonal c ell i := by
    have h := hpp i i
    simp only [if_pos] at h
    rw [← hterminal i i] at h
    rw [forcedPivotDiagonal]
    field_simp [h2]
    linear_combination -c * h + (P i i + P i i) * hc_mul
  have hP : paperPivotCoefficients c b ell = P := by
    funext i j
    by_cases hij : i = j
    · subst j
      simp [paperPivotCoefficients, b, hdiag]
    · simp [paperPivotCoefficients, b, hij]
  have hcode_paper :
      relabelBlockCode (K := K) data.sigma C =
        rankBoxedRowSpace (paperRankBoxedRows c b ell D) := by
    simpa [paperRankBoxedRows, hP, hellFirst, hellDefect] using
      hcode_determined
  exact ⟨k, r, hr_intrinsic, data.k_add_r, data.sigma,
    b, ell, D, hD, hoff, hcode_paper⟩

end BuildingUpFormalization.Components.QaryRankBoxedNormalization
