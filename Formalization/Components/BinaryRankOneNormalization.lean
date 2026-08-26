import Formalization.Components.BinaryRankOneNormalizationDefinitions
import Formalization.Components.BinaryCzKim
import Formalization.Components.Foundations
import Formalization.Components.PermutationEquivalence
import Formalization.Components.RankBoxedConstruction
import Mathlib.Algebra.CharP.Two

set_option autoImplicit false

namespace BuildingUpFormalization.Components.BinaryRankOneNormalization

open BuildingUpFormalization.Components.Foundations
open BuildingUpFormalization.Components.BinaryCzKim
open BuildingUpFormalization.Components.PermutationEquivalence
open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.SplitBoxed

variable {K : Type*} [Field K]

/-- Flattening a rank-box row is a linear equivalence induced solely by a
coordinate equivalence. -/
def flattenRankBoxLinearEquiv {k r : ℕ} :
    RankBoxRow K k r ≃ₗ[K] (Fin (2 * (k + r)) → K) where
  toFun := flattenRankBoxRow
  invFun := fun v x q => v (rankBoxCoordEquivFin k r (x, q))
  left_inv R := by
    funext x q
    simp [flattenRankBoxRow]
  right_inv v := by
    funext j
    simp [flattenRankBoxRow]
  map_add' R S := by
    funext j
    rfl
  map_smul' a R := by
    funext j
    rfl

@[simp] theorem flattenRankBoxLinearEquiv_apply {k r : ℕ}
    (R : RankBoxRow K k r) :
    flattenRankBoxLinearEquiv R = flattenRankBoxRow R := by
  rfl

/-- Flattening preserves the Euclidean product exactly. -/
theorem dot_flattenRankBoxRow {k r : ℕ}
    (R S : RankBoxRow K k r) :
    dot (flattenRankBoxRow R) (flattenRankBoxRow S) =
      rankBoxRowInner R S := by
  unfold dot flattenRankBoxRow rankBoxRowInner splitBlockInner
  rw [← (rankBoxCoordEquivFin k r).sum_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
  rfl

set_option maxHeartbeats 800000 in
/-- Linear independence is unchanged by flattening the two-coordinate
blocks and reindexing the generator rows. -/
theorem flattenRankBoxedRows_linearIndependent {k r : ℕ}
    {R : RankBoxIndex k r → RankBoxRow K k r}
    (hR : LinearIndependent K R) :
    LinearIndependent K (flattenRankBoxedRows R) := by
  let e := flattenRankBoxLinearEquiv (K := K) (k := k) (r := r)
  have hmap : LinearIndependent K (e ∘ R) :=
    LinearIndependent.map' hR e.toLinearMap (LinearEquiv.ker e)
  simpa [flattenRankBoxedRows, Function.comp_def] using
    hmap.comp finSumFinEquiv.symm finSumFinEquiv.symm.injective

/-- In characteristic two, self-orthogonality forces the coordinate sum of
every codeword to vanish. -/
theorem sum_eq_zero_of_dot_self_eq_zero [CharP K 2]
    {n : ℕ} (v : Fin n → K) (hself : dot v v = 0) :
    ∑ i, v i = 0 := by
  have hsquare : (∑ i, v i) ^ 2 = 0 := by
    rw [CharTwo.sum_sq]
    simpa [dot, pow_two] using hself
  exact sq_eq_zero_iff.mp hsquare

/-- Every self-dual code in characteristic two contains the all-ones word.
This is the first invariant used in the Chinburg--Zhang induction. -/
theorem allOnes_mem_of_paperSelfDualCode [CharP K 2]
    {n : ℕ} {C : Submodule K (Fin n → K)}
    (hC : paperSelfDualCode (K := K) C) :
    allOnes (K := K) n ∈ C := by
  rw [hC]
  apply (LinearMap.BilinForm.mem_orthogonal_iff).2
  intro v hv
  rw [LinearMap.BilinForm.isOrtho_def]
  change dot v (allOnes (K := K) n) = 0
  have hvself : dot v v = 0 := by
    have hvorth :
        v ∈ (dotBilin (K := K) (n := n)).orthogonal C := hC ▸ hv
    have hvv :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hvorth) v hv
    simpa [LinearMap.BilinForm.isOrtho_def] using hvv
  simpa [dot, allOnes] using
    sum_eq_zero_of_dot_self_eq_zero v hvself

/-- A subspace of dimension at least two contains a word with two unequal
coordinates.  Otherwise every word would be a scalar multiple of the
all-ones word, forcing dimension at most one. -/
theorem exists_mem_with_unequal_coordinates
    {n : ℕ} {C : Submodule K (Fin n → K)} (i₀ : Fin n)
    (hdim : 2 ≤ Module.finrank K C) :
    ∃ v ∈ C, ∃ i j, v i ≠ v j := by
  by_contra h
  push_neg at h
  have hle : C ≤
      Submodule.span K ({allOnes (K := K) n} : Set (Fin n → K)) := by
    intro v hv
    have heq : v = v i₀ • allOnes (K := K) n := by
      funext j
      simp only [Pi.smul_apply, allOnes, smul_eq_mul, mul_one]
      exact h v hv j i₀
    rw [heq]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_singleton _))
  have hfin := Submodule.finrank_mono hle
  have hspan : Module.finrank K
      (Submodule.span K ({allOnes (K := K) n} : Set (Fin n → K)) ) ≤ 1 := by
    simpa using finrank_span_le_card
      ({allOnes (K := K) n} : Set (Fin n → K))
  omega

/-- Over the binary field, a nonconstant word may be complemented by the
all-ones word so that a selected unequal coordinate pair becomes `01`. -/
theorem exists_mem_with_zero_one_coordinates
    {n : ℕ} {C : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (i₀ : Fin n) (hdim : 2 ≤ Module.finrank (ZMod 2) C)
    (hones : allOnes (K := ZMod 2) n ∈ C) :
    ∃ x ∈ C, ∃ i j, x i = 0 ∧ x j = 1 := by
  obtain ⟨v, hv, i, j, hij⟩ :=
    exists_mem_with_unequal_coordinates i₀ hdim
  have binary_unequal : ∀ (a b : ZMod 2), a ≠ b →
      (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact (hab rfl).elim
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact (hab rfl).elim
  rcases binary_unequal (v i) (v j) hij with h01 | h10
  · exact ⟨v, hv, i, j, h01⟩
  · refine ⟨v + allOnes (K := ZMod 2) n,
      C.add_mem hv hones, i, j, ?_, ?_⟩
    · simp only [Pi.add_apply, h10.1, allOnes]
      exact CharP.cast_eq_zero (ZMod 2) 2
    · simp [h10.2, allOnes]

/-- Every binary self-dual code of length at least four contains a codeword
with an explicitly oriented `01` pivot pair.  This is the row chosen at the
start of the Chinburg--Zhang inductive step. -/
theorem binarySelfDualCode_exists_zero_one_pivot
    {k : ℕ}
    {C : Submodule (ZMod 2) (Fin (2 * (k + 1)) → ZMod 2)}
    (hk : 1 ≤ k) (hC : paperSelfDualCode (K := ZMod 2) C) :
    ∃ x ∈ C, ∃ i j, x i = 0 ∧ x j = 1 := by
  have hhalf :=
    (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
      (K := ZMod 2) (C := C)).mp hC |>.2
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hhalf
  have hdimEq : Module.finrank (ZMod 2) C = k + 1 := by
    apply Nat.mul_left_cancel (by omega : 0 < 2)
    exact hhalf
  have hdim : 2 ≤ Module.finrank (ZMod 2) C := by omega
  let i₀ : Fin (2 * (k + 1)) := ⟨0, by omega⟩
  exact exists_mem_with_zero_one_coordinates i₀ hdim
    (allOnes_mem_of_paperSelfDualCode hC)

theorem pairToHeadPerm_apply_zero {n : ℕ} {i j : Fin (2 + n)}
    (hij : i ≠ j) : pairToHeadPerm i j 0 = i := by
  have hj0 : (Equiv.swap 0 i).symm j ≠ 0 := by
    intro h
    have h' := congrArg (Equiv.swap 0 i) h
    simp at h'
    exact hij h'.symm
  have h01 : (0 : Fin (2 + n)) ≠ 1 := by
    have hone : (1 : Fin (2 + n)) = ⟨1, by omega⟩ := by
      apply Fin.ext
      change 1 % (2 + n) = 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [hone]
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)
  rw [pairToHeadPerm, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne (a := (1 : Fin (2 + n)))
      (b := (Equiv.swap 0 i).symm j) (x := 0) h01 hj0.symm,
    Equiv.swap_apply_left]

theorem pairToHeadPerm_apply_one {n : ℕ} {i j : Fin (2 + n)} :
    pairToHeadPerm i j 1 = j := by
  rw [pairToHeadPerm, Equiv.trans_apply, Equiv.swap_apply_left]
  simp

/-- The selected `01` pair becomes the literal first two scalar coordinates;
the witness remains in the coordinate-permuted code. -/
theorem pairToHeadPerm_orients_pivot
    {n : ℕ} {C : Submodule (ZMod 2) (Fin (2 + n) → ZMod 2)}
    {x : Fin (2 + n) → ZMod 2} (hxC : x ∈ C)
    {i j : Fin (2 + n)} (hx0 : x i = 0) (hx1 : x j = 1) :
    let σ := pairToHeadPerm i j
    let C' := permutedCode (K := ZMod 2) σ C
    let x' := permuteVec σ x
    x' ∈ C' ∧ x' 0 = 0 ∧ x' 1 = 1 := by
  have hij : i ≠ j := by
    intro h
    subst j
    rw [hx0] at hx1
    exact zero_ne_one hx1
  dsimp
  refine ⟨⟨x, hxC, rfl⟩, ?_, ?_⟩
  · simpa [permuteVec, pairToHeadPerm_apply_zero hij] using hx0
  · simpa [permuteVec, pairToHeadPerm_apply_one] using hx1

/-- The displayed rank-one box is not merely a syntactic target: its
diagonal and opposite-block equations certify a binary self-dual code. -/
theorem binaryCzRankOneFinRows_paperSelfDualCode {k : ℕ}
    (b : Fin k → Fin k → ZMod 2)
    (hdiag : ∀ i, b i i = 0)
    (hopposite : ∀ i j, i ≠ j → b i j + b j i = 1) :
    paperSelfDualCode (K := ZMod 2)
      (rowSpace (binaryCzRankOneFinRows b)) := by
  have horthBlock :
      RankBoxedPairwiseOrthogonal (binaryCzRankOneRows b) :=
    binaryCzRankOneRows_pairwiseOrthogonal b hdiag hopposite
  have horthFlat : PairwiseOrthogonal (K := ZMod 2)
      (binaryCzRankOneFinRows b) := by
    intro i j
    change dot
      (flattenRankBoxRow (binaryCzRankOneRows b (finSumFinEquiv.symm i)))
      (flattenRankBoxRow (binaryCzRankOneRows b (finSumFinEquiv.symm j))) = 0
    rw [dot_flattenRankBoxRow]
    exact horthBlock (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  have hlinBlock : LinearIndependent (ZMod 2) (binaryCzRankOneRows b) :=
    rankBoxedRows_linearIndependent_of_core_fullRank 1 b
      (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1)
      binaryCzRankOne_core_fullRank
  have hlinFlat : LinearIndependent (ZMod 2)
      (binaryCzRankOneFinRows b) :=
    flattenRankBoxedRows_linearIndependent hlinBlock
  apply (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
    (K := ZMod 2) (C := rowSpace (binaryCzRankOneFinRows b))).2
  refine ⟨rowSpace_le_orthogonal_of_pairwiseOrthogonal horthFlat, ?_⟩
  rw [show Module.finrank (ZMod 2)
          ↥(rowSpace (binaryCzRankOneFinRows b)) = k + 1 by
        simpa [rowSpace] using finrank_span_eq_card hlinFlat,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

@[simp] theorem binaryHeadDefectLinear_apply
    {K : Type*} [Field K] {n : ℕ} (v : Fin (2 + n) → K) :
    binaryHeadDefectLinear v = v 0 + v 1 := rfl

@[simp] theorem binaryTailLinear_apply
    {K : Type*} [Field K] {n : ℕ} (v : Fin (2 + n) → K) :
    binaryTailLinear v = splitTail (K := K) v := rfl

/-- Deleting an oriented `01` pivot pair is injective on the equal-coordinate
subcode of a binary self-dual code. Orthogonality to the pivot recovers
the common deleted coordinate from the retained tail. -/
theorem binaryShorteningMap_injective
    {n : ℕ}
    {C : Submodule (ZMod 2) (Fin (2 + n) → ZMod 2)}
    {x : Fin (2 + n) → ZMod 2}
    (hC : paperSelfDualCode (K := ZMod 2) C)
    (hxC : x ∈ C) (hx0 : x 0 = 0) (hx1 : x 1 = 1) :
    Function.Injective (binaryShorteningMap C) := by
  have zero_of (v : binaryShorteningDomain C)
      (hv : binaryShorteningMap C v = 0) : v = 0 := by
    have htail : splitTail (K := ZMod 2)
        (v : Fin (2 + n) → ZMod 2) = 0 := by
      exact hv
    have hdefect : (v : Fin (2 + n) → ZMod 2) 0 +
        (v : Fin (2 + n) → ZMod 2) 1 = 0 := v.property
    have heq : (v : Fin (2 + n) → ZMod 2) 0 =
        (v : Fin (2 + n) → ZMod 2) 1 := by
      have hneg : -((v : Fin (2 + n) → ZMod 2) 1) =
          (v : Fin (2 + n) → ZMod 2) 1 := by
        exact CharTwo.neg_eq ((v : Fin (2 + n) → ZMod 2) 1)
      exact (eq_neg_of_add_eq_zero_left hdefect).trans hneg
    have hvC : (v : Fin (2 + n) → ZMod 2) ∈ C := v.1.2
    have hvorth : dot x (v : Fin (2 + n) → ZMod 2) = 0 := by
      have hxorth : x ∈
          (dotBilin (K := ZMod 2) (n := 2 + n)).orthogonal C := hC ▸ hxC
      have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hxorth) v hvC
      simpa [LinearMap.BilinForm.isOrtho_def, dot_comm] using h
    have hv1 : (v : Fin (2 + n) → ZMod 2) 1 = 0 := by
      rw [← prepend2_head_splitTail (K := ZMod 2) x,
        ← prepend2_head_splitTail (K := ZMod 2)
          (v : Fin (2 + n) → ZMod 2)] at hvorth
      rw [dot_prepend2_prepend2] at hvorth
      simp [hx0, hx1, htail, dot] at hvorth
      exact hvorth
    have hv0 : (v : Fin (2 + n) → ZMod 2) 0 = 0 := heq.trans hv1
    apply Subtype.ext
    apply Subtype.ext
    rw [← prepend2_head_splitTail (K := ZMod 2)
      (v : Fin (2 + n) → ZMod 2), hv0, hv1, htail]
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      fin_cases j <;> simp [prepend2, head2]
    · intro j
      simp [prepend2]
  intro v w hvw
  apply sub_eq_zero.mp
  apply zero_of (v - w)
  simpa using congrArg (fun z => z - binaryShorteningMap C w) hvw

/-- The two-coordinate reduction at an oriented `01` pivot is again a
binary self-dual code.  This is the dimension-and-orthogonality step in the
Chinburg--Zhang induction, with no imported classification axiom. -/
theorem binaryShortenedCode_paperSelfDualCode
    {n : ℕ}
    {C : Submodule (ZMod 2) (Fin (2 + n) → ZMod 2)}
    {x : Fin (2 + n) → ZMod 2}
    (hC : paperSelfDualCode (K := ZMod 2) C)
    (hxC : x ∈ C) (hx0 : x 0 = 0) (hx1 : x 1 = 1) :
    paperSelfDualCode (K := ZMod 2) (binaryShortenedCode C) := by
  have hchar :=
    (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
      (K := ZMod 2) (C := C)).mp hC
  apply (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
    (K := ZMod 2) (C := binaryShortenedCode C)).2
  refine ⟨?_, ?_⟩
  · intro y hy
    change ∀ z ∈ binaryShortenedCode C, dot z y = 0
    rcases hy with ⟨u, rfl⟩
    intro z hz
    rcases hz with ⟨v, rfl⟩
    have huC : (u : Fin (2 + n) → ZMod 2) ∈ C := u.1.2
    have hvC : (v : Fin (2 + n) → ZMod 2) ∈ C := v.1.2
    have huv : dot (v : Fin (2 + n) → ZMod 2)
        (u : Fin (2 + n) → ZMod 2) = 0 := hchar.1 huC v hvC
    have hueq : (u : Fin (2 + n) → ZMod 2) 0 =
        (u : Fin (2 + n) → ZMod 2) 1 := by
      have h := u.property
      have hneg : -((u : Fin (2 + n) → ZMod 2) 1) =
          (u : Fin (2 + n) → ZMod 2) 1 :=
        CharTwo.neg_eq _
      exact (eq_neg_of_add_eq_zero_left h).trans hneg
    have hveq : (v : Fin (2 + n) → ZMod 2) 0 =
        (v : Fin (2 + n) → ZMod 2) 1 := by
      have h := v.property
      have hneg : -((v : Fin (2 + n) → ZMod 2) 1) =
          (v : Fin (2 + n) → ZMod 2) 1 :=
        CharTwo.neg_eq _
      exact (eq_neg_of_add_eq_zero_left h).trans hneg
    rw [← prepend2_head_splitTail (K := ZMod 2)
        (v : Fin (2 + n) → ZMod 2),
      ← prepend2_head_splitTail (K := ZMod 2)
        (u : Fin (2 + n) → ZMod 2),
      dot_prepend2_prepend2, hveq, hueq] at huv
    change dot (splitTail (K := ZMod 2) (v : Fin (2 + n) → ZMod 2))
      (splitTail (K := ZMod 2) (u : Fin (2 + n) → ZMod 2)) = 0
    rw [show (v : Fin (2 + n) → ZMod 2) 1 *
        (u : Fin (2 + n) → ZMod 2) 1 +
        (v : Fin (2 + n) → ZMod 2) 1 *
        (u : Fin (2 + n) → ZMod 2) 1 = 0 by
      exact CharTwo.add_self_eq_zero _] at huv
    simpa using huv
  · let f : C →ₗ[ZMod 2] ZMod 2 :=
        (binaryHeadDefectLinear (K := ZMod 2) (n := n)).domRestrict C
    have hsurj : Function.Surjective f := by
      intro a
      refine ⟨⟨a • x, C.smul_mem a hxC⟩, ?_⟩
      dsimp [f]
      rw [hx0, hx1]
      simp
    have hrange : f.range = ⊤ :=
      LinearMap.range_eq_top_of_surjective f hsurj
    have hfdim : Module.finrank (ZMod 2) f.range = 1 := by
      rw [hrange]
      simp
    have hrank := f.finrank_range_add_finrank_ker
    have hdomdim : 2 * Module.finrank (ZMod 2)
        (binaryShorteningDomain C) = n := by
      change 2 * Module.finrank (ZMod 2) f.ker = n
      rw [hfdim] at hrank
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hchar
      omega
    let s : binaryShorteningDomain C →ₗ[ZMod 2] (Fin n → ZMod 2) :=
      binaryShorteningMap C
    have hinj : Function.Injective s :=
      binaryShorteningMap_injective hC hxC hx0 hx1
    have hshortRank := LinearMap.finrank_range_add_finrank_ker
      (K := ZMod 2) s
    have hker : s.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
    rw [hker] at hshortRank
    simp at hshortRank
    change 2 * Module.finrank (ZMod 2) s.range =
      Module.finrank (ZMod 2) (Fin n → ZMod 2)
    rw [hshortRank, hdomdim,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- An oriented pivot and any row family spanning its reduced code reconstruct
the original code as the literal binary Kim building-up row space. -/
theorem orientedPivot_reconstructs_from_shortening
    {m : ℕ}
    {C : Submodule (ZMod 2) (Fin (2 + 2 * m) → ZMod 2)}
    {x : Fin (2 + 2 * m) → ZMod 2}
    (hC : paperSelfDualCode (K := ZMod 2) C)
    (hxC : x ∈ C) (hx0 : x 0 = 0) (hx1 : x 1 = 1)
    {G : Fin m → Fin (2 * m) → ZMod 2}
    (hG : rowSpace G = binaryShortenedCode C) :
    let p := x + allOnes (K := ZMod 2) (2 + 2 * m)
    let z := splitTail (K := ZMod 2) p
    C = rowSpace (buildRowsBin z G) := by
  let p := x + allOnes (K := ZMod 2) (2 + 2 * m)
  let z := splitTail (K := ZMod 2) p
  change C = rowSpace (buildRowsBin z G)
  have hpC : p ∈ C :=
    C.add_mem hxC (allOnes_mem_of_paperSelfDualCode hC)
  have hp0 : p 0 = 1 := by simp [p, hx0, allOnes]
  have hp1 : p 1 = 0 := by
    simp only [p, Pi.add_apply, hx1, allOnes]
    exact CharP.cast_eq_zero (ZMod 2) 2
  have hpSelf : dot p p = 0 := by
    have hpOrth : p ∈
        (dotBilin (K := ZMod 2) (n := 2 + 2 * m)).orthogonal C := hC ▸ hpC
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hpOrth) p hpC
    simpa [LinearMap.BilinForm.isOrtho_def] using h
  have hzNorm : dot z z = 1 := by
    rw [← prepend2_head_splitTail (K := ZMod 2) p,
      dot_prepend2_prepend2, hp0, hp1] at hpSelf
    simpa [z, CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hpSelf
  have hD : paperSelfDualCode (K := ZMod 2) (rowSpace G) := by
    rw [hG]
    exact binaryShortenedCode_paperSelfDualCode hC hxC hx0 hx1
  have hbuild : paperSelfDualCode (K := ZMod 2)
      (rowSpace (buildRowsBin z G)) :=
    paper_binary_kim_building_up_exact hzNorm hD
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [rowSpace]
    apply Submodule.span_le.2
    rintro _ ⟨r, rfl⟩
    rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨i, rfl⟩
    · change prepend2 1 0 z ∈ C
      have hpEq : prepend2 1 0 z = p := by
        simpa [z, hp0, hp1] using
          (prepend2_head_splitTail (K := ZMod 2) p)
      rw [hpEq]
      exact hpC
    · have hGi : G i ∈ binaryShortenedCode C := by
        rw [← hG]
        exact Submodule.subset_span (Set.mem_range_self i)
      rcases hGi with ⟨v, hv⟩
      have hvTail : splitTail (K := ZMod 2)
          (v : Fin (2 + 2 * m) → ZMod 2) = G i := by
        exact hv
      have hvC : (v : Fin (2 + 2 * m) → ZMod 2) ∈ C := v.1.2
      have hveq : (v : Fin (2 + 2 * m) → ZMod 2) 0 =
          (v : Fin (2 + 2 * m) → ZMod 2) 1 := by
        have hd := v.property
        exact (eq_neg_of_add_eq_zero_left hd).trans (CharTwo.neg_eq _)
      have hpv : dot p (v : Fin (2 + 2 * m) → ZMod 2) = 0 := by
        have hpOrth : p ∈
            (dotBilin (K := ZMod 2) (n := 2 + 2 * m)).orthogonal C :=
          hC ▸ hpC
        have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hpOrth) v hvC
        simpa [LinearMap.BilinForm.isOrtho_def, dot_comm] using h
      have hcoeff : (v : Fin (2 + 2 * m) → ZMod 2) 0 =
          dot z (G i) := by
        rw [← prepend2_head_splitTail (K := ZMod 2) p,
          ← prepend2_head_splitTail (K := ZMod 2)
            (v : Fin (2 + 2 * m) → ZMod 2),
          dot_prepend2_prepend2, hp0, hp1, hveq] at hpv
        rw [hvTail] at hpv
        have hv1coeff : (v : Fin (2 + 2 * m) → ZMod 2) 1 =
            dot z (G i) := by
          simpa [z, CharTwo.neg_eq] using
            eq_neg_of_add_eq_zero_left hpv
        exact hveq.trans hv1coeff
      change prepend2 (dot z (G i)) (dot z (G i)) (G i) ∈ C
      rw [← hcoeff]
      have hvEq : prepend2
          ((v : Fin (2 + 2 * m) → ZMod 2) 0)
          ((v : Fin (2 + 2 * m) → ZMod 2) 0) (G i) =
          (v : Fin (2 + 2 * m) → ZMod 2) := by
        have hrec := prepend2_head_splitTail (K := ZMod 2)
          (v : Fin (2 + 2 * m) → ZMod 2)
        simpa only [hveq, hvTail] using hrec
      rw [hvEq]
      exact hvC
  · have hCdim :=
      (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
        (K := ZMod 2) (C := C)).mp hC |>.2
    have hBdim :=
      (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
        (K := ZMod 2) (C := rowSpace (buildRowsBin z G))).mp hbuild |>.2
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hCdim hBdim
    apply Nat.mul_left_cancel (by omega : 0 < 2)
    exact hBdim.trans hCdim.symm

/-- The reverse normalization theorem in the first nonempty length.  A
binary self-dual code of length two is the repetition code generated by
`(1,1)`, which is exactly the rank-one box with no pivot blocks. -/
theorem binarySelfDualCode_has_rankOneNormalForm_lengthTwo
    {C : Submodule (ZMod 2) (Fin 2 → ZMod 2)}
    (hC : paperSelfDualCode (K := ZMod 2) C) :
    HasBinaryCzRankOneNormalForm (k := 0) C := by
  let emptyB : Fin 0 → Fin 0 → ZMod 2 := fun i => Fin.elim0 i
  refine ⟨Equiv.refl _, emptyB, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · have hperm : permutedCode (K := ZMod 2) (Equiv.refl _) C = C := by
      ext v
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [coordinatePermuteLinearEquiv, permuteVec] using hy
      · intro hv
        exact ⟨v, hv, by rfl⟩
    rw [hperm]
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [rowSpace]
      apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      have hi : i = 0 := by omega
      rw [hi, show binaryCzRankOneFinRows emptyB 0 =
          allOnes (K := ZMod 2) 2 by
        funext j
        fin_cases j <;> rfl]
      exact allOnes_mem_of_paperSelfDualCode hC
    · have htarget := binaryCzRankOneFinRows_paperSelfDualCode emptyB
          (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      have hCdim :=
        (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
          (K := ZMod 2) (C := C)).mp hC |>.2
      have htargetDim :=
        (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
          (K := ZMod 2)
          (C := rowSpace (binaryCzRankOneFinRows emptyB))).mp htarget |>.2
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
        Nat.zero_add, Nat.mul_one] at hCdim htargetDim
      apply Nat.mul_left_cancel (by omega : 0 < 2)
      exact htargetDim.trans hCdim.symm

end BuildingUpFormalization.Components.BinaryRankOneNormalization
