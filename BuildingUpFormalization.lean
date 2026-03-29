import Mathlib

open FiniteField
open Matrix
open BigOperators

/-!
# BuildingUpFormalization

This file is organized as a single Lean companion for the current paper version
in `paper_submission/paper.tex`.

## Paper-to-Lean theorem spine

The current paper body is tracked through the following Lean declarations.

### Preliminaries / common algebra
- `dot`, `dotBilin`, `rowSpace`
- `paperSelfDualCode`, `paperLagrangianSubspace`
- `paper_self_dual_iff_lagrangian`
- `paper_dotBilin_nondegenerate`
- `paperHyperbolicPair`, `splitE1`, `splitE2`
- `split_seed_code_self_dual`
- `dotBilin_nondegenerate`

### Binary section
- `buildRowsBin_matrix_gram_zero`
- `codeEquiv_rebuild_of_IsBoxedKimFamily`
- `sameCode_boxedFamily_buildRowsBin`

### q-ary section
- `buildRows_matrix_gram_zero`
- `buildRows_rowSpace_self_dual_of_self_dual_parent_basis`
- `splitBuildFamily_iff_rebuild`
- `exists_unique_split_parent_of_IsSplitBuildFamily`
- `exists_unique_splitBuildFamily_of_parent`
- `exists_splitIsometryCodeEquiv_buildRows_of_pairwiseOrthogonal_isotropicHeadFamily`

### Paper-facing wrappers added at the end of this file
- `paper_binary_cz_kim_equivalence`
- `paper_qary_building_up_rebuild`
- `paper_qary_building_up_forward_self_dual`
- `paper_split_boxed_form_forward_core`
- `paper_conditional_split_boxed_normalization_core`

The small explicit GF(5)/GF(13) application examples are intentionally not part
of the Lean completion target for the current pass.
-/

section GeneralRingIdentities

variable {R : Type*} [CommRing R]

theorem core_identity (c : R) (hc : c ^ 2 = (-1 : R)) :
    1 + c ^ 2 = 0 := by
  rw [hc]
  ring

theorem cross_vanishing (c yi yj : R) (hc : c ^ 2 = (-1 : R)) :
    yi * yj * (1 + c ^ 2) = 0 := by
  rw [core_identity (c := c) hc]
  ring

theorem norm_form_splitting (c x y : R) (hc : c ^ 2 = (-1 : R)) :
    x ^ 2 + y ^ 2 = (x + c * y) * (x - c * y) := by
  calc
    x ^ 2 + y ^ 2 = x ^ 2 - c ^ 2 * y ^ 2 := by rw [hc]; ring
    _ = (x + c * y) * (x - c * y) := by ring

theorem correction_isotropic (c yi : R) (hc : c ^ 2 = (-1 : R)) :
    (-yi) ^ 2 + (-(c * yi)) ^ 2 = 0 := by
  calc
    (-yi) ^ 2 + (-(c * yi)) ^ 2 = yi ^ 2 * (1 + c ^ 2) := by ring
    _ = 0 := by rw [core_identity (c := c) hc]; ring

theorem ri_rj_expand (c yi yj gij : R) :
    (-yi) * (-yj) + (-(c * yi)) * (-(c * yj)) + gij =
      yi * yj * (1 + c ^ 2) + gij := by
  ring

theorem ri_rj_full_orth (c yi yj gij : R)
    (hc : c ^ 2 = (-1 : R)) (hg : gij = 0) :
    (-yi) * (-yj) + (-(c * yi)) * (-(c * yj)) + gij = 0 := by
  rw [ri_rj_expand, hg, core_identity (c := c) hc]
  ring

theorem solomon_tits_identity (q : Int) :
    (q + 1) * (q + 1) - 2 * (q + 1) + 1 = q * q := by
  ring

theorem rank_extension_count (q : ℕ) :
    2 * (q + 1) = 2 + 2 * q := by
  ring

end GeneralRingIdentities

section CommonCore

variable {K : Type*} [Field K]

def dot {n : ℕ} (u v : Fin n → K) : K :=
  ∑ j, u j * v j

theorem dot_comm {n : ℕ} (u v : Fin n → K) :
    dot u v = dot v u := by
  unfold dot
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem dot_add_left {n : ℕ} (u v w : Fin n → K) :
    dot (u + v) w = dot u w + dot v w := by
  unfold dot
  simp [add_mul, Finset.sum_add_distrib]

theorem dot_add_right {n : ℕ} (u v w : Fin n → K) :
    dot u (v + w) = dot u v + dot u w := by
  unfold dot
  simp [mul_add, Finset.sum_add_distrib]

theorem dot_smul_left {n : ℕ} (a : K) (u v : Fin n → K) :
    dot (a • u) v = a * dot u v := by
  unfold dot
  simp [Finset.mul_sum, mul_assoc]

theorem dot_smul_right {n : ℕ} (a : K) (u v : Fin n → K) :
    dot u (a • v) = a * dot u v := by
  rw [dot_comm, dot_smul_left, dot_comm]

def head2 (a b : K) : Fin 2 → K
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

def prepend2 {n : ℕ} (a b : K) (u : Fin n → K) : Fin (2 + n) → K :=
  Fin.append (head2 a b) u

@[simp] theorem prepend2_apply_zero
    {n : ℕ} (a b : K) (u : Fin n → K) :
    prepend2 a b u 0 = a := by
  change Fin.append (head2 a b) u (Fin.castAdd n (0 : Fin 2)) = a
  simpa [prepend2, head2] using
    (Fin.append_left (head2 a b) u (0 : Fin 2))

@[simp] theorem prepend2_apply_one
    {n : ℕ} (a b : K) (u : Fin n → K) :
    prepend2 a b u 1 = b := by
  have h1 : Fin.castAdd n (1 : Fin 2) = (1 : Fin (2 + n)) := by
    apply Fin.ext
    change 1 = 1 % (2 + n)
    have hlt : 1 < 2 + n := by omega
    rw [Nat.mod_eq_of_lt hlt]
  rw [h1.symm]
  simpa [prepend2, head2] using
    (Fin.append_left (head2 a b) u (1 : Fin 2))

def r0 {n : ℕ} (x : Fin n → K) : Fin (2 + n) → K :=
  prepend2 1 0 x

theorem dot_prepend2_prepend2
    {n : ℕ} (a b a' b' : K) (u v : Fin n → K) :
    dot (prepend2 a b u) (prepend2 a' b' v)
      = a * a' + b * b' + dot u v := by
  unfold dot prepend2
  rw [Fin.sum_univ_add]
  simp [head2, Fin.sum_univ_two, add_assoc]

theorem dot_pi_single_right {n : ℕ} (u : Fin n → K) (j : Fin n) :
    dot u (Pi.single j (1 : K)) = u j := by
  classical
  unfold dot
  simp [Pi.single_apply]

theorem dot_pi_single_left {n : ℕ} (u : Fin n → K) (j : Fin n) :
    dot (Pi.single j (1 : K)) u = u j := by
  rw [dot_comm, dot_pi_single_right]

def rowMatrix {m n : ℕ} (R : Fin m → Fin n → K) : Matrix (Fin m) (Fin n) K :=
  fun i j => R i j

theorem rowMatrix_mul_transpose_apply
    {m n : ℕ} (R : Fin m → Fin n → K) (i j : Fin m) :
    (rowMatrix R * (rowMatrix R).transpose) i j = dot (R i) (R j) := by
  unfold rowMatrix dot
  rw [Matrix.mul_apply]
  simp

def rowSpace {m n : ℕ} (R : Fin m → Fin n → K) : Submodule K (Fin n → K) :=
  Submodule.span K (Set.range R)

theorem mem_rowSpace
    {m n : ℕ} (R : Fin m → Fin n → K) (i : Fin m) :
    R i ∈ rowSpace R := by
  rw [rowSpace]
  exact Submodule.subset_span ⟨i, rfl⟩

def dotBilin {n : ℕ} : LinearMap.BilinForm K (Fin n → K) :=
  LinearMap.mk₂ K dot dot_add_left dot_smul_left dot_add_right dot_smul_right

@[simp] theorem dotBilin_apply {n : ℕ} (u v : Fin n → K) :
    dotBilin (K := K) u v = dot u v := by
  simp [dotBilin]

theorem dotBilin_isSymm {n : ℕ} : (dotBilin (K := K) (n := n)).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro u v
  simp [dot_comm]

theorem dotBilin_isRefl {n : ℕ} : (dotBilin (K := K) (n := n)).IsRefl :=
  (dotBilin_isSymm (K := K) (n := n)).isRefl

theorem dotBilin_separatingLeft {n : ℕ} :
    LinearMap.SeparatingLeft (dotBilin (K := K) (n := n)) := by
  intro u hu
  funext j
  have hj := hu (Pi.single j (1 : K))
  simpa [dotBilin, dot_pi_single_right] using hj

theorem dotBilin_separatingRight {n : ℕ} :
    LinearMap.SeparatingRight (dotBilin (K := K) (n := n)) := by
  intro u hu
  funext j
  have hj := hu (Pi.single j (1 : K))
  simpa [dotBilin, dot_pi_single_left] using hj

theorem dotBilin_nondegenerate {n : ℕ} :
    (dotBilin (K := K) (n := n)).Nondegenerate := by
  exact ⟨dotBilin_separatingLeft (K := K) (n := n), dotBilin_separatingRight (K := K) (n := n)⟩

section PaperPreliminaries

def paperSelfDualCode {n : ℕ} (C : Submodule K (Fin n → K)) : Prop :=
  C = (dotBilin (K := K) (n := n)).orthogonal C

def paperLagrangianSubspace {n : ℕ} (L : Submodule K (Fin n → K)) : Prop :=
  L = (dotBilin (K := K) (n := n)).orthogonal L

theorem paper_self_dual_iff_lagrangian
    {n : ℕ} {C : Submodule K (Fin n → K)} :
    paperSelfDualCode (K := K) C ↔ paperLagrangianSubspace (K := K) C := by
  rfl

theorem paper_dotBilin_nondegenerate
    {n : ℕ} :
    (dotBilin (K := K) (n := n)).Nondegenerate := by
  exact dotBilin_nondegenerate (K := K) (n := n)

def paperHyperbolicPair {n : ℕ} (e₁ e₂ : Fin n → K) : Prop :=
  dot e₁ e₁ = 0 ∧ dot e₂ e₂ = 0 ∧ dot e₁ e₂ = 1

def splitE1 (c : K) : Fin 2 → K := head2 1 c

def splitE2 (c : K) : Fin 2 → K := head2 ((2 : K)⁻¹) (-((2 : K)⁻¹ * c))

end PaperPreliminaries

theorem row_mem_dotBilin_orthogonal_of_pairwise_zero
    {m n : ℕ} {R : Fin m → Fin n → K}
    (hR : ∀ i j : Fin m, dot (R i) (R j) = 0)
    (i : Fin m) :
    R i ∈ (dotBilin (K := K) (n := n)).orthogonal (rowSpace R) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  rw [rowSpace] at hw
  refine Submodule.span_induction (p := fun z _ => (dotBilin (K := K) (n := n)).IsOrtho z (R i))
    ?_ ?_ ?_ ?_ hw
  · intro y hy
    rcases hy with ⟨j, rfl⟩
    rw [LinearMap.BilinForm.isOrtho_def]
    simpa [dotBilin, hR j i]
  · simpa using
      (LinearMap.BilinForm.isOrtho_zero_left
        (B := dotBilin (K := K) (n := n)) (x := R i))
  · intro x y hx hy hx0 hy0
    rw [LinearMap.BilinForm.isOrtho_def] at hx0 hy0 ⊢
    have hx0' : dot x (R i) = 0 := by simpa [dotBilin] using hx0
    have hy0' : dot y (R i) = 0 := by simpa [dotBilin] using hy0
    simpa [dotBilin, dot_add_left, hx0', hy0']
  · intro a x hx hx0
    rw [LinearMap.BilinForm.isOrtho_def] at hx0 ⊢
    have hx0' : dot x (R i) = 0 := by simpa [dotBilin] using hx0
    simpa [dotBilin, dot_smul_left, hx0']

theorem rowSpace_le_orthogonal_of_pairwise_zero
    {m n : ℕ} {R : Fin m → Fin n → K}
    (hR : ∀ i j : Fin m, dot (R i) (R j) = 0) :
    rowSpace R ≤ (dotBilin (K := K) (n := n)).orthogonal (rowSpace R) := by
  rw [rowSpace]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact row_mem_dotBilin_orthogonal_of_pairwise_zero (K := K) hR i

def IsIsotropic {n : ℕ} (v : Fin n → K) : Prop :=
  dot v v = 0

def PairwiseOrthogonal {m n : ℕ} (R : Fin m → Fin n → K) : Prop :=
  ∀ i j : Fin m, dot (R i) (R j) = 0

theorem pairwiseOrthogonal_iff
    {m n : ℕ} {R : Fin m → Fin n → K} :
    PairwiseOrthogonal (K := K) R ↔ ∀ i j : Fin m, dot (R i) (R j) = 0 := by
  rfl

theorem rowSpace_le_orthogonal_of_pairwiseOrthogonal
    {m n : ℕ} {R : Fin m → Fin n → K}
    (hR : PairwiseOrthogonal (K := K) R) :
    rowSpace R ≤ (dotBilin (K := K) (n := n)).orthogonal (rowSpace R) := by
  exact rowSpace_le_orthogonal_of_pairwise_zero (K := K) hR

theorem pairwiseOrthogonal_iff_rowSpace_le_orthogonal
    {m n : ℕ} {R : Fin m → Fin n → K} :
    PairwiseOrthogonal (K := K) R ↔
      rowSpace R ≤ (dotBilin (K := K) (n := n)).orthogonal (rowSpace R) := by
  constructor
  · intro hR
    exact rowSpace_le_orthogonal_of_pairwiseOrthogonal (K := K) hR
  · intro hC i j
    have hi : R i ∈ (dotBilin (K := K) (n := n)).orthogonal (rowSpace R) := by
      exact hC (mem_rowSpace R i)
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hi
    have hj : R j ∈ rowSpace R := mem_rowSpace R j
    simpa [LinearMap.BilinForm.isOrtho_def, dotBilin, dot_comm] using hi (R j) hj

theorem dot_pi_single_single
    {n : ℕ} (i j : Fin n) (a b : K) :
    dot (Pi.single i a) (Pi.single j b) = if i = j then a * b else 0 := by
  classical
  unfold dot
  by_cases h : i = j
  · subst h
    simp [Pi.single_apply]
  · have h' : j ≠ i := by
      intro hji
      exact h hji.symm
    simp [Pi.single_apply, h, h', eq_comm]

theorem dot_append_append
    {m n : ℕ}
    (u u' : Fin m → K) (v v' : Fin n → K) :
    dot (Fin.append u v) (Fin.append u' v') = dot u u' + dot v v' := by
  unfold dot
  rw [Fin.sum_univ_add]
  simp

def GramZero {m n : ℕ} (R : Fin m → Fin n → K) : Prop :=
  rowMatrix R * (rowMatrix R).transpose = 0

theorem pairwiseOrthogonal_iff_gramZero
    {m n : ℕ} {R : Fin m → Fin n → K} :
    PairwiseOrthogonal (K := K) R ↔ GramZero (K := K) R := by
  constructor
  · intro hR
    ext i j
    simp [GramZero, rowMatrix_mul_transpose_apply, hR i j]
  · intro hG i j
    have hij := congr_fun (congr_fun hG i) j
    simpa [GramZero, rowMatrix_mul_transpose_apply] using hij

def hyperbolicVecPlus {n : ℕ} (c : K) : Fin (2 + n) → K :=
  prepend2 1 c 0

def hyperbolicVecMinus {n : ℕ} (c : K) : Fin (2 + n) → K :=
  prepend2 1 (-c) 0

theorem hyperbolicVecPlus_isotropic
    {n : ℕ} {c : K} (hc : c ^ 2 = (-1 : K)) :
    IsIsotropic (K := K) (hyperbolicVecPlus (n := n) c) := by
  unfold IsIsotropic hyperbolicVecPlus
  rw [dot_prepend2_prepend2]
  simp [dot]
  calc
    1 + c * c = 1 + c ^ 2 := by rw [pow_two]
    _ = 1 + (-1 : K) := by rw [hc]
    _ = 0 := by ring

theorem hyperbolicVecMinus_isotropic
    {n : ℕ} {c : K} (hc : c ^ 2 = (-1 : K)) :
    IsIsotropic (K := K) (hyperbolicVecMinus (n := n) c) := by
  unfold IsIsotropic hyperbolicVecMinus
  rw [dot_prepend2_prepend2]
  simp [dot]
  calc
    1 + c * c = 1 + c ^ 2 := by rw [pow_two]
    _ = 1 + (-1 : K) := by rw [hc]
    _ = 0 := by ring

theorem dot_hyperbolicVecPlus_hyperbolicVecMinus
    {n : ℕ} {c : K} (hc : c ^ 2 = (-1 : K)) :
    dot (hyperbolicVecPlus (K := K) (n := n) c)
        (hyperbolicVecMinus (K := K) (n := n) c) = (2 : K) := by
  rw [hyperbolicVecPlus, hyperbolicVecMinus, dot_prepend2_prepend2]
  simp [dot]
  have hmul : 1 + c * (-c) = 1 - c * c := by ring
  calc
    1 + -(c * c) = 1 - c * c := by simpa using hmul
    _ = 1 - c ^ 2 := by rw [pow_two]
    _ = 1 - (-1 : K) := by rw [hc]
    _ = (2 : K) := by ring

theorem hyperbolicVecPlus_isotropic_iff
    {n : ℕ} {c : K} :
    IsIsotropic (K := K) (hyperbolicVecPlus (K := K) (n := n) c) ↔
      c ^ 2 = (-1 : K) := by
  unfold IsIsotropic hyperbolicVecPlus
  rw [dot_prepend2_prepend2]
  simp [dot]
  constructor
  · intro h
    have hc := congrArg (fun t : K => t - 1) h
    simpa [pow_two] using hc
  · intro hc
    calc
      1 + c * c = 1 + c ^ 2 := by rw [pow_two]
      _ = 1 + (-1 : K) := by rw [hc]
      _ = 0 := by ring

theorem hyperbolicVecMinus_isotropic_iff
    {n : ℕ} {c : K} :
    IsIsotropic (K := K) (hyperbolicVecMinus (K := K) (n := n) c) ↔
      c ^ 2 = (-1 : K) := by
  unfold IsIsotropic hyperbolicVecMinus
  rw [dot_prepend2_prepend2]
  simp [dot]
  constructor
  · intro h
    have hc := congrArg (fun t : K => t - 1) h
    simpa [pow_two] using hc
  · intro hc
    calc
      1 + c * c = 1 + c ^ 2 := by rw [pow_two]
      _ = 1 + (-1 : K) := by rw [hc]
      _ = 0 := by ring

theorem dot_hyperbolicVecPlus_hyperbolicVecMinus_eq_two_iff
    {n : ℕ} {c : K} :
    dot (hyperbolicVecPlus (K := K) (n := n) c)
        (hyperbolicVecMinus (K := K) (n := n) c) = (2 : K) ↔
      c ^ 2 = (-1 : K) := by
  rw [hyperbolicVecPlus, hyperbolicVecMinus, dot_prepend2_prepend2]
  simp [dot]
  constructor
  · intro h
    have hc : c * c = (1 : K) - 2 := by
      simpa using congrArg (fun t : K => 1 - t) h
    calc
      c ^ 2 = c * c := by rw [pow_two]
      _ = (1 : K) - 2 := hc
      _ = (-1 : K) := by ring
  · intro hc
    calc
      1 + -(c * c) = 1 - c ^ 2 := by rw [pow_two]; ring
      _ = 1 - (-1 : K) := by rw [hc]
      _ = (2 : K) := by ring

end CommonCore

section HyperbolicRealization

theorem exists_sq_neg_one_of_card_mod_four_eq_one
    {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F % 4 = 1) :
    ∃ i : F, i ^ 2 = (-1 : F) := by
  have hneq : Fintype.card F % 4 ≠ 3 := by
    omega
  have hsq : IsSquare (-1 : F) := by
    exact (FiniteField.isSquare_neg_one_iff).2 hneq
  rcases hsq with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simpa [pow_two, mul_comm] using hi.symm

def H2 {K : Type*} [Field K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, (2 : K); (2 : K), 0]

def P_of_root {K : Type*} [Field K] (i : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1, 1; i, -i]

theorem transpose_mul_self_P_of_sq_eq_neg_one
    {K : Type*} [Field K] {i : K}
    (hi : i ^ 2 = (-1 : K)) :
    (P_of_root i).transpose * P_of_root i = H2 := by
  ext a b <;> fin_cases a <;> fin_cases b
  ·
    simp [P_of_root, H2, Matrix.mul_apply]
    calc
      (1 : K) + i * i = 1 + i ^ 2 := by rw [pow_two]
      _ = 1 + (-1 : K) := by rw [hi]
      _ = 0 := by ring
  ·
    simp [P_of_root, H2, Matrix.mul_apply]
    calc
      (1 : K) + -(i * i) = 1 - i ^ 2 := by rw [pow_two]; ring
      _ = 1 - (-1 : K) := by rw [hi]
      _ = (2 : K) := by ring
  ·
    simp [P_of_root, H2, Matrix.mul_apply]
    calc
      (1 : K) + -(i * i) = 1 - i ^ 2 := by rw [pow_two]; ring
      _ = 1 - (-1 : K) := by rw [hi]
      _ = (2 : K) := by ring
  ·
    simp [P_of_root, H2, Matrix.mul_apply]
    calc
      (1 : K) + i * i = 1 + i ^ 2 := by rw [pow_two]
      _ = 1 + (-1 : K) := by rw [hi]
      _ = 0 := by ring

theorem det_P_of_root
    {K : Type*} [Field K] (i : K) :
    Matrix.det (P_of_root i) = -(2 : K) * i := by
  simp [P_of_root, Matrix.det_fin_two]
  ring

theorem root_neg_one_ne_zero
    {K : Type*} [Field K] {i : K}
    (hi : i ^ 2 = (-1 : K)) :
    i ≠ 0 := by
  intro hiz
  have hzero : (0 : K) = (-1 : K) := by
    simpa [hiz, pow_two] using hi
  exact (neg_ne_zero.mpr one_ne_zero) hzero.symm

theorem det_P_of_root_ne_zero
    {K : Type*} [Field K] [Fact ((2 : K) ≠ 0)] {i : K}
    (hi : i ^ 2 = (-1 : K)) :
    Matrix.det (P_of_root i) ≠ 0 := by
  rw [det_P_of_root]
  have h2 : -(2 : K) ≠ 0 := by
    exact neg_ne_zero.mpr Fact.out
  exact mul_ne_zero h2 (root_neg_one_ne_zero hi)

theorem exists_nonsingular_matrix_hyperbolic_of_card_mod_four_eq_one
    {F : Type*} [Field F] [Fintype F] [Fact ((2 : F) ≠ 0)]
    (hF : Fintype.card F % 4 = 1) :
    ∃ P : Matrix (Fin 2) (Fin 2) F,
      P.transpose * P = H2 ∧ Matrix.det P ≠ 0 := by
  rcases exists_sq_neg_one_of_card_mod_four_eq_one (F := F) hF with ⟨i, hi⟩
  refine ⟨P_of_root i, ?_, ?_⟩
  · exact transpose_mul_self_P_of_sq_eq_neg_one (K := F) hi
  · exact det_P_of_root_ne_zero (K := F) hi

end HyperbolicRealization

section NormFormConstruction

variable {K : Type*} [Field K] [Fact ((2 : K) ≠ 0)]

theorem norm_form_witness
    (a c : K) (hc : c ^ 2 = (-1 : K)) :
    let x : K := (1 + a) / 2
    let y : K := ((1 - a) / 2) * c
    x ^ 2 + y ^ 2 = a := by
  dsimp
  have h2 : (2 : K) ≠ 0 := Fact.out
  field_simp [h2]
  rw [hc]
  ring

theorem exists_norm_pair
    (a c : K) (hc : c ^ 2 = (-1 : K)) :
    ∃ x y : K, x ^ 2 + y ^ 2 = a := by
  refine ⟨(1 + a) / 2, ((1 - a) / 2) * c, ?_⟩
  simpa using norm_form_witness (K := K) a c hc

theorem exists_dot_eq_in_two_coordinates
    {n : ℕ} (a c : K) (hc : c ^ 2 = (-1 : K)) :
    ∃ v : Fin (2 + n) → K, dot v v = a := by
  rcases exists_norm_pair (K := K) a c hc with ⟨x, y, hxy⟩
  refine ⟨prepend2 x y (0 : Fin n → K), ?_⟩
  rw [dot_prepend2_prepend2]
  simp [dot]
  simpa [pow_two] using hxy

theorem exists_extension_vector_neg_one
    {n : ℕ} (c : K) (hc : c ^ 2 = (-1 : K)) :
    ∃ v : Fin (2 + n) → K, dot v v = (-1 : K) := by
  simpa using exists_dot_eq_in_two_coordinates (K := K) (n := n) (-1 : K) c hc

end NormFormConstruction

section StandardSeedCodes

variable {K : Type*} [Field K]

def leftHalf {n : ℕ} (v : Fin (n + n) → K) : Fin n → K :=
  fun i => v (Fin.castAdd n i)

def rightHalf {n : ℕ} (v : Fin (n + n) → K) : Fin n → K :=
  fun i => v (Fin.natAdd n i)

def seedEmbedding {n : ℕ} (c : K) (u : Fin n → K) : Fin (n + n) → K :=
  Fin.append u (c • u)

theorem append_leftHalf_rightHalf
    {n : ℕ} (v : Fin (n + n) → K) :
    Fin.append (leftHalf (K := K) v) (rightHalf (K := K) v) = v := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    rw [Fin.append_left]
    rfl
  · intro i
    rw [Fin.append_right]
    rfl

def seedRow {n : ℕ} (c : K) (i : Fin n) : Fin (n + n) → K :=
  Fin.append (Pi.single i 1) (Pi.single i c)

def seedRows {n : ℕ} (c : K) : Fin n → Fin (n + n) → K :=
  fun i => seedRow c i

theorem seedEmbedding_zero
    {n : ℕ} (c : K) :
    seedEmbedding (K := K) (n := n) c 0 = 0 := by
  funext j
  exact Fin.addCases
    (fun i => by simp [seedEmbedding])
    (fun i => by
      rw [seedEmbedding, Fin.append_right]
      simp [Pi.smul_apply])
    j

theorem seedEmbedding_add
    {n : ℕ} (c : K) (u v : Fin n → K) :
    seedEmbedding (K := K) c (u + v) =
      seedEmbedding (K := K) c u + seedEmbedding (K := K) c v := by
  funext j
  exact Fin.addCases
    (fun i => by simp [seedEmbedding])
    (fun i => by
      rw [Pi.add_apply]
      repeat rw [seedEmbedding, Fin.append_right]
      simp [Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, mul_add])
    j

theorem seedEmbedding_smul
    {n : ℕ} (a c : K) (u : Fin n → K) :
    seedEmbedding (K := K) c (a • u) =
      a • seedEmbedding (K := K) c u := by
  funext j
  exact Fin.addCases
    (fun i => by simp [seedEmbedding, Pi.smul_apply])
    (fun i => by
      rw [Pi.smul_apply]
      repeat rw [seedEmbedding, Fin.append_right]
      simp [Pi.smul_apply, smul_eq_mul,
        mul_assoc, mul_left_comm, mul_comm])
    j

theorem seedEmbedding_sum
    {α : Type*} [DecidableEq α] {n : ℕ} (s : Finset α) (f : α → Fin n → K) (c : K) :
    seedEmbedding (K := K) c (Finset.sum s f) =
      Finset.sum s (fun a => seedEmbedding (K := K) c (f a)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [seedEmbedding_zero]
  · intro a s ha hs
    simp [Finset.sum_insert, ha, seedEmbedding_add, hs]

theorem seedRow_eq_seedEmbedding_single
    {n : ℕ} (c : K) (i : Fin n) :
    seedRow (K := K) c i = seedEmbedding (K := K) c (Pi.single i 1) := by
  funext j
  exact Fin.addCases
    (fun k => by
      simpa [seedRow, seedEmbedding, Pi.single_apply])
    (fun k => by
      rw [seedRow, seedEmbedding, Fin.append_right, Fin.append_right, Pi.smul_apply]
      by_cases h : k = i
      · subst h
        simp [Pi.single_apply, smul_eq_mul]
      · simp [Pi.single_apply, h, smul_eq_mul])
    j

theorem dot_pi_single_right_scalar
    {n : ℕ} (u : Fin n → K) (i : Fin n) (a : K) :
    dot u (Pi.single i a) = a * u i := by
  classical
  unfold dot
  simp [Pi.single_apply, mul_comm, mul_left_comm, mul_assoc]

theorem dot_append_seedRow
    {n : ℕ} (a b : Fin n → K) (c : K) (i : Fin n) :
    dot (Fin.append a b) (seedRow (K := K) c i) = a i + c * b i := by
  simp [seedRow, dot_append_append, dot_pi_single_right, dot_pi_single_right_scalar]

theorem sum_smul_pi_single
    {n : ℕ} (u : Fin n → K) (c : K) :
    (∑ i, u i • (Pi.single i c : Fin n → K)) = c • u := by
  funext k
  simp [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_comm, mul_left_comm, mul_assoc]

theorem seedEmbedding_eq_sum_seedRows
    {n : ℕ} (c : K) (u : Fin n → K) :
    seedEmbedding (K := K) c u = ∑ i, u i • seedRows (K := K) (n := n) c i := by
  have hu :
      u = ∑ i, u i • (Pi.single i (1 : K) : Fin n → K) := by
    simpa using (sum_smul_pi_single (K := K) u (1 : K)).symm
  calc
    seedEmbedding (K := K) c u
        = seedEmbedding (K := K) c (Finset.sum Finset.univ
            (fun i => u i • (Pi.single i (1 : K) : Fin n → K))) := by
          conv_lhs => rw [hu]
    _ = Finset.sum Finset.univ
          (fun i => seedEmbedding (K := K) c (u i • (Pi.single i (1 : K) : Fin n → K))) := by
          rw [seedEmbedding_sum]
    _ = ∑ i, u i • seedRows (K := K) (n := n) c i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [seedEmbedding_smul, seedRows, seedRow_eq_seedEmbedding_single]

theorem seedEmbedding_mem_rowSpace
    {n : ℕ} (c : K) (u : Fin n → K) :
    seedEmbedding (K := K) c u ∈ rowSpace (seedRows (K := K) (n := n) c) := by
  classical
  rw [seedEmbedding_eq_sum_seedRows]
  exact Submodule.sum_mem _ (fun i hi =>
    Submodule.smul_mem _ _ (mem_rowSpace (seedRows (K := K) (n := n) c) i))

theorem dot_seedRow_seedRow
    {n : ℕ} {c : K} (hc : c ^ 2 = (-1 : K))
    (i j : Fin n) :
    dot (seedRow (K := K) c i) (seedRow (K := K) c j) = 0 := by
  rw [seedRow, seedRow, dot_append_append]
  rw [dot_pi_single_single, dot_pi_single_single]
  by_cases h : i = j
  · subst h
    simp
    have hone : (1 : K) * 1 + c * c = 1 + c * c := by ring
    calc
      1 + c * c = 1 + c * c := by simpa using hone
      _ = 1 + c ^ 2 := by rw [pow_two]
      _ = 1 + (-1 : K) := by rw [hc]
      _ = 0 := by ring
  · simp [h]

theorem seedRows_orthogonal
    {n : ℕ} {c : K} (hc : c ^ 2 = (-1 : K)) :
    PairwiseOrthogonal (K := K) (seedRows (K := K) (n := n) c) := by
  intro i j
  exact dot_seedRow_seedRow (K := K) hc i j

theorem seedRows_matrix_gram_zero
    {n : ℕ} {c : K} (hc : c ^ 2 = (-1 : K)) :
    rowMatrix (seedRows (K := K) (n := n) c) *
      (rowMatrix (seedRows (K := K) (n := n) c)).transpose = 0 := by
  ext i j
  rw [rowMatrix_mul_transpose_apply]
  exact dot_seedRow_seedRow (K := K) hc i j

theorem seedRows_pairwiseOrthogonal_iff_gramZero
    {n : ℕ} {c : K} :
    PairwiseOrthogonal (K := K) (seedRows (K := K) (n := n) c) ↔
      GramZero (K := K) (seedRows (K := K) (n := n) c) := by
  exact pairwiseOrthogonal_iff_gramZero (K := K) (R := seedRows (K := K) (n := n) c)

theorem seedRows_pairwiseOrthogonal_iff_rowSpace_le_orthogonal
    {n : ℕ} {c : K} :
    PairwiseOrthogonal (K := K) (seedRows (K := K) (n := n) c) ↔
      rowSpace (seedRows (K := K) (n := n) c) ≤
        (dotBilin (K := K) (n := n + n)).orthogonal
          (rowSpace (seedRows (K := K) (n := n) c)) := by
  exact pairwiseOrthogonal_iff_rowSpace_le_orthogonal
    (K := K) (R := seedRows (K := K) (n := n) c)

theorem seedRows_gramZero_iff_rowSpace_le_orthogonal
    {n : ℕ} {c : K} :
    GramZero (K := K) (seedRows (K := K) (n := n) c) ↔
      rowSpace (seedRows (K := K) (n := n) c) ≤
        (dotBilin (K := K) (n := n + n)).orthogonal
          (rowSpace (seedRows (K := K) (n := n) c)) := by
  rw [← seedRows_pairwiseOrthogonal_iff_gramZero (K := K) (n := n) (c := c)]
  exact seedRows_pairwiseOrthogonal_iff_rowSpace_le_orthogonal
    (K := K) (n := n) (c := c)

theorem seedRows_rowSpace_le_orthogonal
    {n : ℕ} {c : K} (hc : c ^ 2 = (-1 : K)) :
    rowSpace (seedRows (K := K) (n := n) c) ≤
      (dotBilin (K := K) (n := n + n)).orthogonal
        (rowSpace (seedRows (K := K) (n := n) c)) := by
  exact rowSpace_le_orthogonal_of_pairwiseOrthogonal (K := K)
    (seedRows_orthogonal (K := K) (n := n) hc)

theorem seedRows_orthogonal_le_rowSpace
    {n : ℕ} {c : K} (hc : c ^ 2 = (-1 : K)) :
    (dotBilin (K := K) (n := n + n)).orthogonal
        (rowSpace (seedRows (K := K) (n := n) c)) ≤
      rowSpace (seedRows (K := K) (n := n) c) := by
  intro v hv
  let a := leftHalf (K := K) v
  have hright : rightHalf (K := K) v = c • a := by
    funext i
    have hi := hv (seedRows (K := K) (n := n) c i)
      (mem_rowSpace (seedRows (K := K) (n := n) c) i)
    rw [LinearMap.BilinForm.isOrtho_def] at hi
    rw [← append_leftHalf_rightHalf (K := K) v] at hi
    have hi' :
        dot (Fin.append (leftHalf (K := K) v) (rightHalf (K := K) v))
          (seedRow (K := K) c i) = 0 := by
      simpa [dotBilin, seedRows, dot_comm] using hi
    have hdot : a i + c * rightHalf (K := K) v i = 0 := by
      rw [dot_append_seedRow] at hi'
      simpa [a] using hi'
    have hmul : c * a i + c * (c * rightHalf (K := K) v i) = 0 := by
      simpa [mul_add, mul_assoc] using congrArg (fun t : K => c * t) hdot
    have hmul' : c * a i + c ^ 2 * rightHalf (K := K) v i = 0 := by
      simpa [pow_two, mul_assoc] using hmul
    have hsub : c * a i - rightHalf (K := K) v i = 0 := by
      rw [hc] at hmul'
      simpa [sub_eq_add_neg] using hmul'
    have hEq : c * a i = rightHalf (K := K) v i := sub_eq_zero.mp hsub
    simpa [a, Pi.smul_apply, smul_eq_mul] using hEq.symm
  have hvEq : v = seedEmbedding (K := K) c a := by
    rw [← append_leftHalf_rightHalf (K := K) v]
    simp [seedEmbedding, hright, a]
  rw [hvEq]
  exact seedEmbedding_mem_rowSpace (K := K) c a

theorem seedRows_rowSpace_eq_orthogonal
    {n : ℕ} {c : K} (hc : c ^ 2 = (-1 : K)) :
    rowSpace (seedRows (K := K) (n := n) c) =
      (dotBilin (K := K) (n := n + n)).orthogonal
        (rowSpace (seedRows (K := K) (n := n) c)) := by
  apply le_antisymm
  · exact seedRows_rowSpace_le_orthogonal (K := K) (n := n) hc
  · exact seedRows_orthogonal_le_rowSpace (K := K) (n := n) hc

theorem split_seed_code_self_dual
    {n : ℕ} {c : K} (hc : c ^ 2 = (-1 : K)) :
    rowSpace (seedRows (K := K) (n := n) c) =
      (dotBilin (K := K) (n := n + n)).orthogonal
        (rowSpace (seedRows (K := K) (n := n) c)) := by
  exact seedRows_rowSpace_eq_orthogonal (K := K) (n := n) hc

theorem seedRows_equivalent_conditions
    {n : ℕ} {c : K} (hc : c ^ 2 = (-1 : K)) :
    PairwiseOrthogonal (K := K) (seedRows (K := K) (n := n) c) ∧
      GramZero (K := K) (seedRows (K := K) (n := n) c) ∧
      rowSpace (seedRows (K := K) (n := n) c) ≤
        (dotBilin (K := K) (n := n + n)).orthogonal
          (rowSpace (seedRows (K := K) (n := n) c)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact seedRows_orthogonal (K := K) (n := n) hc
  · exact (seedRows_pairwiseOrthogonal_iff_gramZero (K := K) (n := n) (c := c)).1
      (seedRows_orthogonal (K := K) (n := n) hc)
  · exact seedRows_rowSpace_le_orthogonal (K := K) (n := n) hc

theorem exists_split_seed_code
    {n : ℕ} (c : K) (hc : c ^ 2 = (-1 : K)) :
    ∃ G : Fin n → Fin (n + n) → K,
      rowSpace G =
        (dotBilin (K := K) (n := n + n)).orthogonal (rowSpace G) := by
  refine ⟨seedRows (K := K) (n := n) c, ?_⟩
  exact split_seed_code_self_dual (K := K) (n := n) hc

theorem exists_extension_vector_for_split_seed_code
    {n : ℕ} [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    ∃ x : Fin ((n + 1) + (n + 1)) → K, dot x x = (-1 : K) := by
  have hlen : (n + 1) + (n + 1) = 2 + (n + n) := by omega
  rw [hlen]
  exact exists_extension_vector_neg_one (K := K) (n := n + n) c hc

theorem exists_split_seed_buildingUp_data
    {n : ℕ} [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    ∃ G : Fin (n + 1) → Fin ((n + 1) + (n + 1)) → K,
      rowSpace G =
        (dotBilin (K := K) (n := (n + 1) + (n + 1))).orthogonal (rowSpace G) ∧
      ∃ x : Fin ((n + 1) + (n + 1)) → K, dot x x = (-1 : K) := by
  refine ⟨seedRows (K := K) (n := n + 1) c, ?_, ?_⟩
  · exact split_seed_code_self_dual (K := K) (n := n + 1) hc
  · exact exists_extension_vector_for_split_seed_code (K := K) (n := n) c hc

end StandardSeedCodes

section SplitBuildingUp

variable {K : Type*} [Field K]

def ri {n : ℕ} (c yi : K) (g : Fin n → K) : Fin (2 + n) → K :=
  prepend2 (-yi) (-(c * yi)) g

def buildRows {m n : ℕ} (x : Fin n → K) (c : K) (G : Fin m → Fin n → K) :
    Fin (m + 1) → Fin (2 + n) → K :=
  Fin.cases (r0 x) (fun i => ri c (dot x (G i)) (G i))

theorem dot_r0_r0
    {n : ℕ} {x : Fin n → K}
    (hx : dot x x = (-1 : K)) :
    dot (r0 x) (r0 x) = 0 := by
  rw [r0, dot_prepend2_prepend2]
  rw [hx]
  ring

theorem dot_r0_ri
    {n : ℕ} {x g : Fin n → K} {c yi : K}
    (hyi : yi = dot x g) :
    dot (r0 x) (ri c yi g) = 0 := by
  rw [r0, ri, dot_prepend2_prepend2]
  rw [hyi]
  ring

theorem dot_ri_ri
    {n : ℕ} {g h : Fin n → K} {c yi yj : K}
    (hc : c ^ 2 = (-1 : K))
    (hgh : dot g h = 0) :
    dot (ri c yi g) (ri c yj h) = 0 := by
  rw [ri, ri, dot_prepend2_prepend2]
  rw [hgh]
  calc
    (-yi) * (-yj) + (-(c * yi)) * (-(c * yj)) + 0
        = yi * yj + (c * yi) * (c * yj) := by ring
    _ = yi * yj + (c ^ 2) * (yi * yj) := by
        rw [pow_two]
        ring
    _ = yi * yj + (-1 : K) * (yi * yj) := by rw [hc]
    _ = 0 := by ring

theorem correction_term_eq_smul_isotropic_vector
    {n : ℕ} (c yi : K) :
    prepend2 (-yi) (-(c * yi)) (0 : Fin n → K) =
      (-yi) • prepend2 1 c (0 : Fin n → K) := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    fin_cases k <;> simp [prepend2, head2] <;> ring
  · intro k
    simp [prepend2, head2]

theorem ri_eq_correction_add_tail
    {n : ℕ} (c yi : K) (g : Fin n → K) :
    ri c yi g =
      prepend2 (-yi) (-(c * yi)) (0 : Fin n → K) + prepend2 0 0 g := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    fin_cases k <;> simp [ri, prepend2, head2] <;> ring
  · intro k
    simp [ri, prepend2, head2]

theorem ri_eq_smul_isotropic_vector_add_tail
    {n : ℕ} (c yi : K) (g : Fin n → K) :
    ri c yi g =
      (-yi) • prepend2 1 c (0 : Fin n → K) + prepend2 0 0 g := by
  rw [ri_eq_correction_add_tail, correction_term_eq_smul_isotropic_vector]

theorem isotropic_vector_is_isotropic
    {n : ℕ} {c : K}
    (hc : c ^ 2 = (-1 : K)) :
    dot (prepend2 1 c (0 : Fin n → K)) (prepend2 1 c (0 : Fin n → K)) = 0 := by
  rw [dot_prepend2_prepend2]
  simp [dot]
  calc
    1 + c * c = 1 + c ^ 2 := by rw [pow_two]
    _ = 1 + (-1 : K) := by rw [hc]
    _ = 0 := by ring

theorem correction_term_is_isotropic
    {n : ℕ} {c yi : K}
    (hc : c ^ 2 = (-1 : K)) :
    dot (prepend2 (-yi) (-(c * yi)) (0 : Fin n → K))
        (prepend2 (-yi) (-(c * yi)) (0 : Fin n → K)) = 0 := by
  rw [correction_term_eq_smul_isotropic_vector]
  rw [dot_smul_left, dot_smul_right, isotropic_vector_is_isotropic (K := K) (n := n) hc]
  ring

theorem dot_ri_ri_expand
    {n : ℕ} {g h : Fin n → K} {c yi yj : K} :
    dot (ri c yi g) (ri c yj h) = yi * yj * (1 + c ^ 2) + dot g h := by
  rw [ri, ri, dot_prepend2_prepend2]
  ring

theorem dot_r0_prepend2_on_isotropic_line
    {n : ℕ} (x g : Fin n → K) (c a : K) :
    dot (r0 x) (prepend2 a (c * a) g) = a + dot x g := by
  rw [r0, dot_prepend2_prepend2]
  ring

theorem prepend2_on_isotropic_line_orthogonal_iff
    {n : ℕ} (x g : Fin n → K) (c a : K) :
    dot (r0 x) (prepend2 a (c * a) g) = 0 ↔ a = -dot x g := by
  rw [dot_r0_prepend2_on_isotropic_line (K := K) x g c a]
  constructor
  · intro h
    exact eq_neg_of_add_eq_zero_left h
  · intro h
    rw [h]
    ring

theorem prepend2_on_isotropic_line_eq_ri_iff
    {n : ℕ} (x g : Fin n → K) (c a : K) :
    prepend2 a (c * a) g = ri c (dot x g) g ↔
      dot (r0 x) (prepend2 a (c * a) g) = 0 := by
  rw [prepend2_on_isotropic_line_orthogonal_iff (K := K) x g c a]
  constructor
  · intro h
    have h0 := congrArg (fun v : Fin (2 + n) → K => v 0) h
    simpa [ri, prepend2, head2] using h0
  · intro h
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro k
      fin_cases k
      · simp [ri, prepend2, head2, h]
      · simp [ri, prepend2, head2, h, mul_assoc, mul_left_comm, mul_comm]
    · intro k
      simp [ri, prepend2, head2]

theorem exists_unique_on_isotropic_line_orthogonal_to_r0
    {n : ℕ} (x g : Fin n → K) (c : K) :
    ∃! a : K, dot (r0 x) (prepend2 a (c * a) g) = 0 := by
  refine ⟨-dot x g, ?_, ?_⟩
  · exact (prepend2_on_isotropic_line_orthogonal_iff (K := K) x g c (-dot x g)).2 rfl
  · intro a ha
    exact (prepend2_on_isotropic_line_orthogonal_iff (K := K) x g c a).1 ha

theorem buildRows_succ_universality_iff
    {m n : ℕ} (x : Fin n → K) (c a : K) (G : Fin m → Fin n → K) (i : Fin m) :
    prepend2 a (c * a) (G i) = buildRows x c G (Fin.succ i) ↔
      dot (r0 x) (prepend2 a (c * a) (G i)) = 0 := by
  simpa [buildRows] using
    prepend2_on_isotropic_line_eq_ri_iff (K := K) x (G i) c a

def splitTail {n : ℕ} (v : Fin (2 + n) → K) : Fin n → K :=
  fun j => v (Fin.natAdd 2 j)

def deleteHyperbolicPairSplit {m n : ℕ}
    (R : Fin (m + 1) → Fin (2 + n) → K) : Fin m → Fin n → K :=
  fun i => splitTail (R (Fin.succ i))

theorem splitTail_prepend2
    {n : ℕ} (a b : K) (u : Fin n → K) :
    splitTail (K := K) (prepend2 a b u) = u := by
  funext j
  simp [splitTail, prepend2]

def splitTailLinear {n : ℕ} : (Fin (2 + n) → K) →ₗ[K] (Fin n → K) where
  toFun := splitTail (K := K)
  map_add' := by
    intro u v
    funext j
    simp [splitTail]
  map_smul' := by
    intro a u
    funext j
    simp [splitTail]

@[simp] theorem splitTailLinear_apply
    {n : ℕ} (v : Fin (2 + n) → K) :
    splitTailLinear (K := K) v = splitTail (K := K) v := by
  rfl

theorem splitTail_r0
    {n : ℕ} (x : Fin n → K) :
    splitTail (K := K) (r0 x) = x := by
  simpa [r0] using splitTail_prepend2 (K := K) 1 0 x

theorem splitTail_ri
    {n : ℕ} (c yi : K) (g : Fin n → K) :
    splitTail (K := K) (ri c yi g) = g := by
  simpa [ri] using splitTail_prepend2 (K := K) (-yi) (-(c * yi)) g

def HasIsotropicHead {n : ℕ} (c : K) (v : Fin (2 + n) → K) : Prop :=
  ∃ a : K, ∃ g : Fin n → K, v = prepend2 a (c * a) g

theorem hasIsotropicHead_prepend2
    {n : ℕ} (c a : K) (g : Fin n → K) :
    HasIsotropicHead (K := K) c (prepend2 a (c * a) g) := by
  exact ⟨a, g, rfl⟩

theorem hasIsotropicHead_ri
    {n : ℕ} (x g : Fin n → K) (c : K) :
    HasIsotropicHead (K := K) c (ri c (dot x g) g) := by
  refine ⟨-dot x g, g, ?_⟩
  simp [ri]

theorem prepend2_eq_smul_prepend2_normalizedHead
    {n : ℕ} {a b : K} (ha : a ≠ 0) (g : Fin n → K) :
    prepend2 a b g =
      a • prepend2 1 (b / a) ((a⁻¹) • g) := by
  have hab : a * (b / a) = b := by
    field_simp [div_eq_mul_inv, ha]
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    fin_cases k
    · simp [prepend2, head2]
    · simpa [prepend2, head2, Pi.smul_apply, smul_eq_mul] using hab.symm
  · intro k
    simp [prepend2, head2, Pi.smul_apply, smul_eq_mul, ha, mul_assoc]

theorem sq_eq_neg_one_of_head_sq_zero_of_ne_zero
    {a b : K} (ha : a ≠ 0) (hhead : a ^ 2 + b ^ 2 = 0) :
    (b / a) ^ 2 = (-1 : K) := by
  have ha2 : a ^ 2 ≠ (0 : K) := by
    exact pow_ne_zero 2 ha
  have hmul : a ^ 2 * ((b / a) ^ 2 + 1) = 0 := by
    calc
      a ^ 2 * ((b / a) ^ 2 + 1) = a ^ 2 + b ^ 2 := by
        field_simp [pow_two, ha]
        ring
      _ = 0 := hhead
  have hsum : (b / a) ^ 2 + 1 = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_left ha2
  exact eq_neg_of_add_eq_zero_left hsum

theorem exists_normalized_head_of_head_sq_zero_of_ne_zero
    {n : ℕ} {a b : K} (g : Fin n → K)
    (ha : a ≠ 0) (hhead : a ^ 2 + b ^ 2 = 0) :
    ∃ c : K, c ^ 2 = (-1 : K) ∧
      HasIsotropicHead (K := K) c (prepend2 a b g) ∧
      prepend2 a b g = a • prepend2 1 c ((a⁻¹) • g) := by
  refine ⟨b / a, sq_eq_neg_one_of_head_sq_zero_of_ne_zero (K := K) ha hhead, ?_, ?_⟩
  · refine ⟨a, g, ?_⟩
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro k
      fin_cases k
      · simp [prepend2, head2]
      · simp [prepend2, head2, div_eq_mul_inv, ha, mul_assoc, mul_left_comm, mul_comm]
    · intro k
      simp [prepend2, head2]
  · exact prepend2_eq_smul_prepend2_normalizedHead (K := K) ha g

theorem dot_r0_smul_prepend2_one_c_iff
    {n : ℕ} (x g : Fin n → K) (c a : K) (ha : a ≠ 0) :
    dot (r0 x) (a • prepend2 1 c g) = 0 ↔ dot x g = (-1 : K) := by
  rw [dot_smul_right]
  constructor
  · intro h
    have h0 : dot (r0 x) (prepend2 1 c g) = 0 := by
      exact (mul_eq_zero.mp h).resolve_left ha
    have h0' : dot (r0 x) (prepend2 1 (c * 1) g) = 0 := by
      simpa [mul_one] using h0
    have h1 : (1 : K) = -dot x g := by
      simpa using
        (prepend2_on_isotropic_line_orthogonal_iff (K := K) x g c (1 : K)).1 h0'
    have h2 : (-1 : K) = dot x g := by
      simpa using congrArg Neg.neg h1
    simpa using h2.symm
  · intro h
    have h0' : dot (r0 x) (prepend2 1 (c * 1) g) = 0 := by
      have h1 : (1 : K) = -dot x g := by
        rw [h]
        ring
      simpa using
        (prepend2_on_isotropic_line_orthogonal_iff (K := K) x g c (1 : K)).2 h1
    have h0 : dot (r0 x) (prepend2 1 c g) = 0 := by
      simpa [mul_one] using h0'
    rw [h0]
    ring

theorem exists_normalized_head_orthogonal_to_r0_of_head_sq_zero_of_ne_zero
    {n : ℕ} (x : Fin n → K) {a b : K} (g : Fin n → K)
    (ha : a ≠ 0) (hhead : a ^ 2 + b ^ 2 = 0)
    (hortho : dot (r0 x) (prepend2 a b g) = 0) :
    ∃ c : K, c ^ 2 = (-1 : K) ∧
      prepend2 a b g = a • prepend2 1 c ((a⁻¹) • g) ∧
      dot x ((a⁻¹) • g) = (-1 : K) := by
  rcases exists_normalized_head_of_head_sq_zero_of_ne_zero (K := K) g ha hhead with
    ⟨c, hc, _, hEq⟩
  refine ⟨c, hc, hEq, ?_⟩
  have hScaled : dot (r0 x) (a • prepend2 1 c ((a⁻¹) • g)) = 0 := by
    simpa [hEq] using hortho
  exact (dot_r0_smul_prepend2_one_c_iff (K := K) x ((a⁻¹) • g) c a ha).1 hScaled

theorem ri_of_dot_eq_neg_one
    {n : ℕ} {x g : Fin n → K} (c : K)
    (h : dot x g = (-1 : K)) :
    ri c (dot x g) g = prepend2 1 c g := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    fin_cases k
    · simp [ri, prepend2, head2, h]
    · simp [ri, prepend2, head2, h]
  · intro k
    simp [ri, prepend2, head2]

theorem exists_scaled_ri_of_head_sq_zero_of_ne_zero_and_orthogonal
    {n : ℕ} (x : Fin n → K) {a b : K} (g : Fin n → K)
    (ha : a ≠ 0) (hhead : a ^ 2 + b ^ 2 = 0)
    (hortho : dot (r0 x) (prepend2 a b g) = 0) :
    ∃ c : K, ∃ g' : Fin n → K,
      c ^ 2 = (-1 : K) ∧
      dot x g' = (-1 : K) ∧
      prepend2 a b g = a • ri c (dot x g') g' := by
  rcases exists_normalized_head_orthogonal_to_r0_of_head_sq_zero_of_ne_zero
      (K := K) x g ha hhead hortho with
    ⟨c, hc, hEq, hdot⟩
  refine ⟨c, (a⁻¹) • g, hc, hdot, ?_⟩
  rw [hEq]
  rw [ri_of_dot_eq_neg_one (K := K) (x := x) c hdot]

theorem head_sq_zero_of_sq_eq_neg_one
    (c a : K) (hc : c ^ 2 = (-1 : K)) :
    a ^ 2 + (c * a) ^ 2 = 0 := by
  calc
    a ^ 2 + (c * a) ^ 2 = a ^ 2 + c ^ 2 * a ^ 2 := by
      rw [pow_two, pow_two]
      ring
    _ = a ^ 2 + (-1 : K) * a ^ 2 := by rw [hc]
    _ = 0 := by ring

theorem dot_prepend2_one_c_prepend2_a_ca
    {n : ℕ} (x g : Fin n → K) (c a : K) :
    dot (prepend2 1 c x) (prepend2 a (c * a) g) =
      a * (1 + c ^ 2) + dot x g := by
  rw [dot_prepend2_prepend2]
  ring

theorem dot_prepend2_a_ca_prepend2_b_cb
    {n : ℕ} (g h : Fin n → K) (c a b : K) :
    dot (prepend2 a (c * a) g) (prepend2 b (c * b) h) =
      a * b * (1 + c ^ 2) + dot g h := by
  rw [dot_prepend2_prepend2]
  ring

theorem orthogonal_to_prepend2_one_c_iff_dot_tail_zero
    {n : ℕ} (x g : Fin n → K) (c a : K)
    (hc : c ^ 2 = (-1 : K)) :
    dot (prepend2 1 c x) (prepend2 a (c * a) g) = 0 ↔ dot x g = 0 := by
  rw [dot_prepend2_one_c_prepend2_a_ca (K := K) x g c a, hc]
  ring_nf

theorem orthogonal_prepend2_a_ca_iff_dot_tail_zero
    {n : ℕ} (g h : Fin n → K) (c a b : K)
    (hc : c ^ 2 = (-1 : K)) :
    dot (prepend2 a (c * a) g) (prepend2 b (c * b) h) = 0 ↔ dot g h = 0 := by
  rw [dot_prepend2_a_ca_prepend2_b_cb (K := K) g h c a b, hc]
  ring_nf

theorem exists_scaled_ri_of_prepend2_on_isotropic_line_orthogonal
    {n : ℕ} (x : Fin n → K) (c a : K) (g : Fin n → K)
    (hc : c ^ 2 = (-1 : K)) (ha : a ≠ 0)
    (hortho : dot (r0 x) (prepend2 a (c * a) g) = 0) :
    ∃ g' : Fin n → K,
      dot x g' = (-1 : K) ∧
      prepend2 a (c * a) g = a • ri c (dot x g') g' := by
  rcases exists_scaled_ri_of_head_sq_zero_of_ne_zero_and_orthogonal
      (K := K) x (a := a) (b := c * a) g ha
      (head_sq_zero_of_sq_eq_neg_one (K := K) c a hc) hortho with
    ⟨c', g', hc', hdot, hEq⟩
  have hcEq : c' = c := by
    let j : Fin (2 + n) := ⟨1, by omega⟩
    have h1 := congrArg (fun v : Fin (2 + n) → K => v j) hEq
    have hmul : c * a = a * c' := by
      simp [j, ri, prepend2, head2, hdot, hc', mul_assoc] at h1
      exact h1
    have hmul' : a * c' = a * c := by
      simpa [mul_comm] using hmul.symm
    exact mul_left_cancel₀ ha hmul'
  refine ⟨g', hdot, ?_⟩
  simpa [hcEq] using hEq

theorem exists_scaled_successor_data_of_fixed_isotropic_head_family
    {m n : ℕ} (x : Fin n → K) (c : K)
    (R : Fin (m + 1) → Fin (2 + n) → K)
    (hc : c ^ 2 = (-1 : K))
    (hs : ∀ i : Fin m, ∃ a : K, a ≠ 0 ∧ ∃ g : Fin n → K,
      R (Fin.succ i) = prepend2 a (c * a) g ∧
        dot (r0 x) (R (Fin.succ i)) = 0) :
    ∀ i : Fin m, ∃ a : K, a ≠ 0 ∧ ∃ g' : Fin n → K,
      dot x g' = (-1 : K) ∧
      R (Fin.succ i) = a • ri c (dot x g') g' := by
  intro i
  rcases hs i with ⟨a, ha, g, hrow, horth⟩
  refine ⟨a, ha, ?_⟩
  rcases exists_scaled_ri_of_prepend2_on_isotropic_line_orthogonal
      (K := K) x c a g hc ha (by simpa [hrow] using horth) with
    ⟨g', hdot, hEq⟩
  exact ⟨g', hdot, hrow.trans hEq⟩

theorem succ_eq_ri_of_hasIsotropicHead_and_orthogonal_to_r0
    {n : ℕ} (x : Fin n → K) (c : K) (v : Fin (2 + n) → K)
    (hhead : HasIsotropicHead (K := K) c v)
    (hortho : dot (r0 x) v = 0) :
    v = ri c (dot x (splitTail (K := K) v)) (splitTail (K := K) v) := by
  rcases hhead with ⟨a, g, rfl⟩
  simpa [splitTail_prepend2] using
    (prepend2_on_isotropic_line_eq_ri_iff (K := K) x g c a).2 hortho

def IsSplitBuildFamily {m n : ℕ}
    (x : Fin n → K) (c : K) (R : Fin (m + 1) → Fin (2 + n) → K) : Prop :=
  R 0 = r0 x ∧
  ∀ i : Fin m,
    HasIsotropicHead (K := K) c (R (Fin.succ i)) ∧
      dot (r0 x) (R (Fin.succ i)) = 0

def IsPivotNormalizedFamily {m n : ℕ}
    (x : Fin n → K) (c : K) (R : Fin (m + 1) → Fin (2 + n) → K) : Prop :=
  R 0 = prepend2 1 c x ∧
  ∀ i : Fin m, ∃ a : K, ∃ g : Fin n → K, R (Fin.succ i) = prepend2 a (c * a) g

def IsOrthogonalTailFamily {m n : ℕ}
    (x : Fin n → K) (G : Fin m → Fin n → K) : Prop :=
  (∀ i : Fin m, dot x (G i) = 0) ∧
    PairwiseOrthogonal (K := K) G

def IsPivotTailFamily {m n : ℕ}
    (x : Fin n → K) (G : Fin m → Fin n → K) : Prop :=
  dot x x = 0 ∧
    IsOrthogonalTailFamily (K := K) x G

theorem pivotNormalizedFamily_tail_orthogonal_to_pivot
    {m n : ℕ} {x : Fin n → K} {c : K}
    {R : Fin (m + 1) → Fin (2 + n) → K}
    (hc : c ^ 2 = (-1 : K))
    (hR : IsPivotNormalizedFamily (K := K) x c R)
    (horth : PairwiseOrthogonal (K := K) R) :
    ∀ i : Fin m, dot x (deleteHyperbolicPairSplit (K := K) R i) = 0 := by
  intro i
  rcases hR with ⟨h0, hs⟩
  rcases hs i with ⟨a, g, hrow⟩
  have hij : dot (R 0) (R (Fin.succ i)) = 0 := horth 0 (Fin.succ i)
  rw [h0, hrow] at hij
  have htail : dot x g = 0 :=
    (orthogonal_to_prepend2_one_c_iff_dot_tail_zero (K := K) x g c a hc).1 hij
  simpa [deleteHyperbolicPairSplit, hrow, splitTail_prepend2] using htail

theorem pivotNormalizedFamily_deleteHyperbolicPairSplit_pairwiseOrthogonal
    {m n : ℕ} {x : Fin n → K} {c : K}
    {R : Fin (m + 1) → Fin (2 + n) → K}
    (hc : c ^ 2 = (-1 : K))
    (hR : IsPivotNormalizedFamily (K := K) x c R)
    (horth : PairwiseOrthogonal (K := K) R) :
    PairwiseOrthogonal (K := K) (deleteHyperbolicPairSplit (K := K) R) := by
  intro i j
  rcases hR with ⟨_, hs⟩
  rcases hs i with ⟨a, g, hrowi⟩
  rcases hs j with ⟨b, h, hrowj⟩
  have hij : dot (R (Fin.succ i)) (R (Fin.succ j)) = 0 := horth (Fin.succ i) (Fin.succ j)
  rw [hrowi, hrowj] at hij
  have htail : dot g h = 0 :=
    (orthogonal_prepend2_a_ca_iff_dot_tail_zero (K := K) g h c a b hc).1 hij
  simpa [deleteHyperbolicPairSplit, hrowi, hrowj, splitTail_prepend2] using htail

theorem pivotNormalizedFamily_deleteHyperbolicPairSplit_isOrthogonalTailFamily
    {m n : ℕ} {x : Fin n → K} {c : K}
    {R : Fin (m + 1) → Fin (2 + n) → K}
    (hc : c ^ 2 = (-1 : K))
    (hR : IsPivotNormalizedFamily (K := K) x c R)
    (horth : PairwiseOrthogonal (K := K) R) :
    IsOrthogonalTailFamily (K := K) x (deleteHyperbolicPairSplit (K := K) R) := by
  refine ⟨?_, ?_⟩
  · exact pivotNormalizedFamily_tail_orthogonal_to_pivot (K := K) hc hR horth
  · exact pivotNormalizedFamily_deleteHyperbolicPairSplit_pairwiseOrthogonal
      (K := K) hc hR horth

theorem pivotNormalizedFamily_pivotTail_isotropic
    {m n : ℕ} {x : Fin n → K} {c : K}
    {R : Fin (m + 1) → Fin (2 + n) → K}
    (hc : c ^ 2 = (-1 : K))
    (hR : IsPivotNormalizedFamily (K := K) x c R)
    (horth : PairwiseOrthogonal (K := K) R) :
    dot x x = 0 := by
  rcases hR with ⟨h0, _⟩
  have h00 : dot (R 0) (R 0) = 0 := horth 0 0
  have hc' : c * c = (-1 : K) := by simpa [pow_two] using hc
  rw [h0, dot_prepend2_prepend2, hc'] at h00
  ring_nf at h00
  exact h00

theorem pivotNormalizedFamily_deleteHyperbolicPairSplit_isPivotTailFamily
    {m n : ℕ} {x : Fin n → K} {c : K}
    {R : Fin (m + 1) → Fin (2 + n) → K}
    (hc : c ^ 2 = (-1 : K))
    (hR : IsPivotNormalizedFamily (K := K) x c R)
    (horth : PairwiseOrthogonal (K := K) R) :
    IsPivotTailFamily (K := K) x (deleteHyperbolicPairSplit (K := K) R) := by
  refine ⟨?_, ?_⟩
  · exact pivotNormalizedFamily_pivotTail_isotropic (K := K) hc hR horth
  · exact pivotNormalizedFamily_deleteHyperbolicPairSplit_isOrthogonalTailFamily
      (K := K) hc hR horth

def pivotRows {m n : ℕ}
    (x : Fin n → K) (c : K) (a : Fin m → K) (G : Fin m → Fin n → K) :
    Fin (m + 1) → Fin (2 + n) → K :=
  Fin.cases (prepend2 1 c x) (fun i => prepend2 (a i) (c * a i) (G i))

def pivotResidualTails {m n : ℕ}
    (x : Fin n → K) (a : Fin m → K) (G : Fin m → Fin n → K) :
    Fin m → Fin n → K :=
  fun i => G i - a i • x

def pivotPureTailRows {m n : ℕ}
    (x : Fin n → K) (c : K) (a : Fin m → K) (G : Fin m → Fin n → K) :
    Fin (m + 1) → Fin (2 + n) → K :=
  Fin.cases (prepend2 1 c x)
    (fun i => prepend2 0 0 (pivotResidualTails x a G i))

def headAlignFamilyVec {n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (v : Fin (2 + n) → K) : Fin (2 + n) → K :=
  prepend2 ((v 0 - c * v 1) / 2) ((v 0 + c * v 1) / 2) (splitTail (K := K) v)

def headAlignFamily {m n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (R : Fin m → Fin (2 + n) → K) :
    Fin m → Fin (2 + n) → K :=
  fun i => headAlignFamilyVec (K := K) c (R i)

def headUnalignFamilyVec {n : ℕ}
    (c : K) (v : Fin (2 + n) → K) : Fin (2 + n) → K :=
  prepend2 (v 0 + v 1) (c * (v 0 - v 1)) (splitTail (K := K) v)

theorem prepend2_head_splitTail
    {n : ℕ} (v : Fin (2 + n) → K) :
    prepend2 (v 0) (v 1) (splitTail (K := K) v) = v := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    rw [prepend2]
    rw [Fin.append_left]
    fin_cases k
    · rfl
    · have h1 : Fin.castAdd n (1 : Fin 2) = (1 : Fin (2 + n)) := by
        apply Fin.ext
        change 1 = 1 % (2 + n)
        have hlt : 1 < 2 + n := by omega
        rw [Nat.mod_eq_of_lt hlt]
      change v 1 = v (Fin.castAdd n (1 : Fin 2))
      rw [h1]
  · intro k
    rw [prepend2]
    rw [Fin.append_right]
    simp [splitTail]

theorem headAlignFamilyVec_prepend2
    {n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c a b : K) (g : Fin n → K) :
    headAlignFamilyVec (K := K) c (prepend2 a b g) =
      prepend2 ((a - c * b) / 2) ((a + c * b) / 2) g := by
  simp [headAlignFamilyVec, splitTail_prepend2]

theorem headUnalignFamilyVec_prepend2
    {n : ℕ} (c a b : K) (g : Fin n → K) :
    headUnalignFamilyVec (K := K) c (prepend2 a b g) =
      prepend2 (a + b) (c * (a - b)) g := by
  simp [headUnalignFamilyVec, splitTail_prepend2]

theorem splitTail_headAlignFamilyVec
    {n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (v : Fin (2 + n) → K) :
    splitTail (K := K) (headAlignFamilyVec (K := K) c v) =
      splitTail (K := K) v := by
  simp [headAlignFamilyVec, splitTail_prepend2]

theorem splitTail_headUnalignFamilyVec
    {n : ℕ} (c : K) (v : Fin (2 + n) → K) :
    splitTail (K := K) (headUnalignFamilyVec (K := K) c v) =
      splitTail (K := K) v := by
  simp [headUnalignFamilyVec, splitTail_prepend2]

theorem headAlignFamilyVec_add
    {n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (u v : Fin (2 + n) → K) :
    headAlignFamilyVec (K := K) c (u + v) =
      headAlignFamilyVec (K := K) c u + headAlignFamilyVec (K := K) c v := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    fin_cases k
    · change (((u 0 + v 0) - c * (u 1 + v 1)) / 2) =
          (u 0 - c * u 1) / 2 + (v 0 - c * v 1) / 2
      ring
    · change (((u 0 + v 0) + c * (u 1 + v 1)) / 2) =
          (u 0 + c * u 1) / 2 + (v 0 + c * v 1) / 2
      ring
  · intro k
    simp [headAlignFamilyVec, splitTail, prepend2]

theorem headAlignFamilyVec_smul
    {n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c a : K) (u : Fin (2 + n) → K) :
    headAlignFamilyVec (K := K) c (a • u) =
      a • headAlignFamilyVec (K := K) c u := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    fin_cases k
    · change ((a * u 0 - c * (a * u 1)) / 2) = a * ((u 0 - c * u 1) / 2)
      ring
    · change ((a * u 0 + c * (a * u 1)) / 2) = a * ((u 0 + c * u 1) / 2)
      ring
  · intro k
    simp [headAlignFamilyVec, splitTail, prepend2, Pi.smul_apply, smul_eq_mul]

theorem headAlignFamilyVec_prepend2_a_ca
    {n : ℕ} [Fact ((2 : K) ≠ 0)] (c : K)
    (hc : c ^ 2 = (-1 : K))
    (a : K) (g : Fin n → K) :
    headAlignFamilyVec (K := K) c (prepend2 a (c * a) g) =
      prepend2 a 0 g := by
  have h2 : (2 : K) ≠ 0 := Fact.out
  rw [headAlignFamilyVec_prepend2 (K := K) c a (c * a) g]
  have hmul : c * (c * a) = -a := by
    calc
      c * (c * a) = (c * c) * a := by ring
      _ = (c ^ 2) * a := by rw [pow_two]
      _ = (-1 : K) * a := by rw [hc]
      _ = -a := by ring
  have hfirst : (a - c * (c * a)) / 2 = a := by
    apply (div_eq_iff h2).2
    rw [hmul]
    ring
  have hsecond : (a + c * (c * a)) / 2 = 0 := by
    apply (div_eq_iff h2).2
    rw [hmul]
    ring
  simp [hfirst, hsecond]

theorem headAlignFamilyVec_headUnalignFamilyVec
    {n : ℕ} [Fact ((2 : K) ≠ 0)] (c : K)
    (hc : c ^ 2 = (-1 : K))
    (v : Fin (2 + n) → K) :
    headAlignFamilyVec (K := K) c (headUnalignFamilyVec (K := K) c v) = v := by
  have h2 : (2 : K) ≠ 0 := Fact.out
  rw [headUnalignFamilyVec, headAlignFamilyVec_prepend2 (K := K) c
    (v 0 + v 1) (c * (v 0 - v 1)) (splitTail (K := K) v)]
  have hmul : c * (c * (v 0 - v 1)) = -(v 0 - v 1) := by
    calc
      c * (c * (v 0 - v 1)) = (c * c) * (v 0 - v 1) := by ring
      _ = (c ^ 2) * (v 0 - v 1) := by rw [pow_two]
      _ = (-1 : K) * (v 0 - v 1) := by rw [hc]
      _ = -(v 0 - v 1) := by ring
  have hfirst : ((v 0 + v 1) - c * (c * (v 0 - v 1))) / 2 = v 0 := by
    apply (div_eq_iff h2).2
    rw [hmul]
    ring
  have hsecond : ((v 0 + v 1) + c * (c * (v 0 - v 1))) / 2 = v 1 := by
    apply (div_eq_iff h2).2
    rw [hmul]
    ring
  simpa [hfirst, hsecond] using prepend2_head_splitTail (K := K) v

theorem headUnalignFamilyVec_headAlignFamilyVec
    {n : ℕ} [Fact ((2 : K) ≠ 0)] (c : K)
    (hc : c ^ 2 = (-1 : K))
    (v : Fin (2 + n) → K) :
    headUnalignFamilyVec (K := K) c (headAlignFamilyVec (K := K) c v) = v := by
  have h2 : (2 : K) ≠ 0 := Fact.out
  rw [headAlignFamilyVec, headUnalignFamilyVec_prepend2 (K := K) c
    ((v 0 - c * v 1) / 2) ((v 0 + c * v 1) / 2) (splitTail (K := K) v)]
  have hfirst : (v 0 - c * v 1) / 2 + (v 0 + c * v 1) / 2 = v 0 := by
    calc
      (v 0 - c * v 1) / 2 + (v 0 + c * v 1) / 2
          = ((v 0 - c * v 1) + (v 0 + c * v 1)) / 2 := by ring
      _ = v 0 := by
        apply (div_eq_iff h2).2
        ring
  have hsecond : c * ((v 0 - c * v 1) / 2 - (v 0 + c * v 1) / 2) = v 1 := by
    calc
      c * ((v 0 - c * v 1) / 2 - (v 0 + c * v 1) / 2)
          = (c * ((v 0 - c * v 1) - (v 0 + c * v 1))) / 2 := by ring
      _ = (((-c ^ 2) * ((2 : K) * v 1))) / 2 := by ring
      _ = ((2 : K) * v 1) / 2 := by rw [hc]; ring
      _ = v 1 := by
        apply (div_eq_iff h2).2
        ring
  simpa [hfirst, hsecond] using prepend2_head_splitTail (K := K) v

def headAlignLinearEquiv {n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (hc : c ^ 2 = (-1 : K)) :
    (Fin (2 + n) → K) ≃ₗ[K] (Fin (2 + n) → K) where
  toFun := headAlignFamilyVec (K := K) c
  invFun := headUnalignFamilyVec (K := K) c
  left_inv := headUnalignFamilyVec_headAlignFamilyVec (K := K) c hc
  right_inv := headAlignFamilyVec_headUnalignFamilyVec (K := K) c hc
  map_add' := headAlignFamilyVec_add (K := K) c
  map_smul' := headAlignFamilyVec_smul (K := K) c

theorem headAlignFamilyVec_pivot
    {n : ℕ} [Fact ((2 : K) ≠ 0)] (c : K)
    (hc : c ^ 2 = (-1 : K))
    (x : Fin n → K) :
    headAlignFamilyVec (K := K) c (prepend2 1 c x) = r0 x := by
  simpa [r0, one_mul] using
    headAlignFamilyVec_prepend2_a_ca (K := K) (n := n) c hc (1 : K) x

theorem headAlignFamilyVec_oppositeHyperbolicHead
    {n : ℕ} [Fact ((2 : K) ≠ 0)] (c : K)
    (hc : c ^ 2 = (-1 : K))
    (x : Fin n → K) :
    headAlignFamilyVec (K := K) c (prepend2 1 (-c) x) =
      prepend2 0 1 x := by
  rw [headAlignFamilyVec_prepend2 (K := K) c 1 (-c) x]
  have h2 : (2 : K) ≠ 0 := Fact.out
  have hc' : c * c = (-1 : K) := by
    simpa [pow_two] using hc
  have hfirst : (1 + c * c) / 2 = 0 := by
    apply (div_eq_iff h2).2
    rw [hc']
    ring
  have hsecond : (1 + -(c * c)) / 2 = 1 := by
    apply (div_eq_iff h2).2
    rw [hc']
    ring
  simp [hfirst, hsecond]

theorem headAlignLinearEquiv_hyperbolicBasis
    {n : ℕ} [Fact ((2 : K) ≠ 0)] (c : K)
    (hc : c ^ 2 = (-1 : K))
    (x : Fin n → K) :
    headAlignLinearEquiv (K := K) (n := n) c hc (prepend2 1 c x) = r0 x ∧
    headAlignLinearEquiv (K := K) (n := n) c hc (prepend2 1 (-c) x) = prepend2 0 1 x := by
  constructor
  · exact headAlignFamilyVec_pivot (K := K) (n := n) c hc x
  · exact headAlignFamilyVec_oppositeHyperbolicHead (K := K) (n := n) c hc x

theorem headAlignFamilyVec_zeroHead
    {n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (g : Fin n → K) :
    headAlignFamilyVec (K := K) c (prepend2 0 0 g) =
      prepend2 0 0 g := by
  rw [headAlignFamilyVec_prepend2 (K := K) c 0 0 g]
  simp

theorem pivotPureTailRows_eq_pivotRows_zero_residual
    {m n : ℕ} (x : Fin n → K) (c : K) (a : Fin m → K) (G : Fin m → Fin n → K) :
    pivotPureTailRows x c a G =
      pivotRows x c (fun _ => 0) (pivotResidualTails x a G) := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [pivotPureTailRows, pivotRows]
  · simp [pivotPureTailRows, pivotRows]

theorem deleteHyperbolicPairSplit_pivotPureTailRows
    {m n : ℕ} (x : Fin n → K) (c : K) (a : Fin m → K) (G : Fin m → Fin n → K) :
    deleteHyperbolicPairSplit (K := K) (pivotPureTailRows x c a G) =
      pivotResidualTails x a G := by
  funext i
  funext j
  rw [deleteHyperbolicPairSplit]
  simp [splitTail, pivotPureTailRows, pivotResidualTails, prepend2]

theorem deleteHyperbolicPairSplit_pivotRows
    {m n : ℕ} (x : Fin n → K) (c : K) (a : Fin m → K) (G : Fin m → Fin n → K) :
    deleteHyperbolicPairSplit (K := K) (pivotRows x c a G) = G := by
  funext i
  funext j
  rw [deleteHyperbolicPairSplit]
  simp [splitTail, pivotRows, prepend2]

theorem pivotRows_isPivotNormalizedFamily
    {m n : ℕ} (x : Fin n → K) (c : K) (a : Fin m → K) (G : Fin m → Fin n → K) :
    IsPivotNormalizedFamily (K := K) x c (pivotRows x c a G) := by
  constructor
  · simp [pivotRows]
  · intro i
    exact ⟨a i, G i, by simp [pivotRows]⟩

theorem pivotRows_succ_eq_smul_zero_add_pureTail
    {m n : ℕ} (x : Fin n → K) (c : K) (a : Fin m → K) (G : Fin m → Fin n → K)
    (i : Fin m) :
    pivotRows x c a G (Fin.succ i) =
      a i • pivotRows x c a G 0 + pivotPureTailRows x c a G (Fin.succ i) := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    fin_cases k
    · simp [pivotRows, pivotPureTailRows, prepend2, head2, Pi.smul_apply, smul_eq_mul]
    · simp [pivotRows, pivotPureTailRows, prepend2, head2, Pi.smul_apply, smul_eq_mul,
        mul_assoc, mul_left_comm, mul_comm]
  · intro k
    simp [pivotRows, pivotPureTailRows, pivotResidualTails, prepend2, head2,
      Pi.smul_apply, smul_eq_mul]

theorem pivotPureTailRows_succ_eq_sub_smul_zero
    {m n : ℕ} (x : Fin n → K) (c : K) (a : Fin m → K) (G : Fin m → Fin n → K)
    (i : Fin m) :
    pivotPureTailRows x c a G (Fin.succ i) =
      pivotRows x c a G (Fin.succ i) - a i • pivotRows x c a G 0 := by
  rw [pivotRows_succ_eq_smul_zero_add_pureTail (K := K) x c a G i]
  abel

theorem pivotResidualTails_isOrthogonalTailFamily
    {m n : ℕ} {x : Fin n → K} {a : Fin m → K} {G : Fin m → Fin n → K}
    (hpack : IsPivotTailFamily (K := K) x G) :
    IsOrthogonalTailFamily (K := K) x (pivotResidualTails x a G) := by
  rcases hpack with ⟨hxx, hxG, hGG⟩
  refine ⟨?_, ?_⟩
  · intro i
    rw [pivotResidualTails, sub_eq_add_neg, dot_add_right]
    have hneg : dot x (-(a i • x)) = 0 := by
      have hnegsmul : -(a i • x) = (-1 : K) • (a i • x) := by simp
      rw [hnegsmul, dot_smul_right, dot_smul_right, hxx]
      ring
    simpa [hxG i] using hneg
  · intro i j
    rw [pivotResidualTails, pivotResidualTails, sub_eq_add_neg, sub_eq_add_neg,
      dot_add_left, dot_add_right, dot_add_right]
    have h1 : dot (G i) (-(a j • x)) = 0 := by
      have hnegsmul : -(a j • x) = (-1 : K) • (a j • x) := by simp
      rw [hnegsmul, dot_smul_right, dot_smul_right, dot_comm (G i) x, hxG i]
      ring
    have h2 : dot (-(a i • x)) (G j) = 0 := by
      have hnegsmul : -(a i • x) = (-1 : K) • (a i • x) := by simp
      rw [dot_comm, hnegsmul, dot_smul_right, dot_smul_right, dot_comm (G j) x, hxG j]
      ring
    have h3 : dot (-(a i • x)) (-(a j • x)) = 0 := by
      have hnegsmul_i : -(a i • x) = (-1 : K) • (a i • x) := by simp
      have hnegsmul_j : -(a j • x) = (-1 : K) • (a j • x) := by simp
      rw [hnegsmul_i, hnegsmul_j, dot_smul_left, dot_smul_right,
        dot_smul_left, dot_smul_right, hxx]
      ring
    simpa [hGG i j, h1, h2, h3]

theorem exists_pivotRows_eq_of_IsPivotNormalizedFamily
    {m n : ℕ} {x : Fin n → K} {c : K}
    {R : Fin (m + 1) → Fin (2 + n) → K}
    (hR : IsPivotNormalizedFamily (K := K) x c R) :
    ∃ a : Fin m → K, ∃ G : Fin m → Fin n → K, R = pivotRows x c a G := by
  rcases hR with ⟨h0, hs⟩
  choose a G hsucc using hs
  refine ⟨a, G, ?_⟩
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simpa [pivotRows] using h0
  · simpa [pivotRows] using hsucc j

theorem pivotRows_pairwiseOrthogonal
    {m n : ℕ} {x : Fin n → K} {c : K} {a : Fin m → K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K))
    (hx : dot x x = 0)
    (hG : IsOrthogonalTailFamily (K := K) x G) :
    PairwiseOrthogonal (K := K) (pivotRows x c a G) := by
  rcases hG with ⟨hxG, hpair⟩
  intro i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · have hc' : c * c = (-1 : K) := by simpa [pow_two] using hc
      simp [pivotRows, dot_prepend2_prepend2, hc', hx]
    · simpa [pivotRows] using
        (orthogonal_to_prepend2_one_c_iff_dot_tail_zero
          (K := K) x (G j') c (a j') hc).2 (hxG j')
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · rw [dot_comm]
      simpa [pivotRows] using
        (orthogonal_to_prepend2_one_c_iff_dot_tail_zero
          (K := K) x (G i') c (a i') hc).2 (hxG i')
    · simpa [pivotRows] using
        (orthogonal_prepend2_a_ca_iff_dot_tail_zero
          (K := K) (G i') (G j') c (a i') (a j') hc).2 (hpair i' j')

theorem pivotRows_pairwiseOrthogonal_iff
    {m n : ℕ} {x : Fin n → K} {c : K} {a : Fin m → K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K)) :
    PairwiseOrthogonal (K := K) (pivotRows x c a G) ↔
      IsPivotTailFamily (K := K) x G := by
  constructor
  · intro horth
    have hR := pivotRows_isPivotNormalizedFamily (K := K) x c a G
    have hpack := pivotNormalizedFamily_deleteHyperbolicPairSplit_isPivotTailFamily
      (K := K) (R := pivotRows x c a G) hc hR horth
    simpa [deleteHyperbolicPairSplit_pivotRows (K := K) x c a G] using hpack
  · intro hpack
    exact pivotRows_pairwiseOrthogonal (K := K) hc hpack.1 hpack.2

theorem pivotPureTailRows_pairwiseOrthogonal
    {m n : ℕ} {x : Fin n → K} {c : K} {a : Fin m → K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K))
    (hpack : IsPivotTailFamily (K := K) x G) :
    PairwiseOrthogonal (K := K) (pivotPureTailRows x c a G) := by
  have hres : IsOrthogonalTailFamily (K := K) x (pivotResidualTails x a G) :=
    pivotResidualTails_isOrthogonalTailFamily (K := K) hpack
  rw [pivotPureTailRows_eq_pivotRows_zero_residual (K := K) x c a G]
  exact
    (pivotRows_pairwiseOrthogonal (K := K) (x := x) (c := c) (a := fun _ => 0)
      (G := pivotResidualTails x a G) hc hpack.1 hres)

theorem headAlignFamily_pivotPureTailRows_eq_buildRows
    {m n : ℕ} [Fact ((2 : K) ≠ 0)]
    {x : Fin n → K} {c : K} {a : Fin m → K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K))
    (horth : IsOrthogonalTailFamily (K := K) x (pivotResidualTails x a G)) :
    headAlignFamily (K := K) c (pivotPureTailRows x c a G) =
      buildRows x c (pivotResidualTails x a G) := by
  rcases horth with ⟨hxG, _⟩
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [headAlignFamily, pivotPureTailRows]
    exact headAlignFamilyVec_pivot (K := K) (n := n) c hc x
  · rw [headAlignFamily]
    simp [pivotPureTailRows, headAlignFamilyVec_zeroHead]
    simp [buildRows, ri, hxG j]

theorem deleteHyperbolicPairSplit_buildRows
    {m n : ℕ} (x : Fin n → K) (c : K) (G : Fin m → Fin n → K) :
    deleteHyperbolicPairSplit (K := K) (buildRows x c G) = G := by
  funext i
  funext j
  rw [deleteHyperbolicPairSplit]
  simp [splitTail, buildRows, ri, prepend2]

theorem buildRows_deleteHyperbolicPairSplit_eq
    {m n : ℕ} {x : Fin n → K} {c : K}
    {R : Fin (m + 1) → Fin (2 + n) → K}
    (hR : IsSplitBuildFamily (K := K) x c R) :
    buildRows x c (deleteHyperbolicPairSplit (K := K) R) = R := by
  rcases hR with ⟨h0, hs⟩
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [buildRows, h0]
  · have hj := hs j
    rcases hj with ⟨hhead, horth⟩
    simp [buildRows]
    symm
    simpa [deleteHyperbolicPairSplit] using
      succ_eq_ri_of_hasIsotropicHead_and_orthogonal_to_r0
        (K := K) x c (R (Fin.succ j)) hhead horth

theorem buildRows_isSplitBuildFamily
    {m n : ℕ} (x : Fin n → K) (c : K) (G : Fin m → Fin n → K) :
    IsSplitBuildFamily (K := K) x c (buildRows x c G) := by
  constructor
  · simp [IsSplitBuildFamily, buildRows]
  · intro i
    constructor
    · simpa [buildRows] using hasIsotropicHead_ri (K := K) x (G i) c
    · simp [buildRows]
      exact dot_r0_ri rfl

theorem buildRows_succ_characterization
    {m n : ℕ} (x : Fin n → K) (c : K) (G : Fin m → Fin n → K)
    (i : Fin m) (v : Fin (2 + n) → K) :
    v = buildRows x c G (Fin.succ i) ↔
      HasIsotropicHead (K := K) c v ∧
        splitTail (K := K) v = G i ∧
        dot (r0 x) v = 0 := by
  constructor
  · intro hv
    subst hv
    refine ⟨?_, ?_, ?_⟩
    · simpa [buildRows] using hasIsotropicHead_ri (K := K) x (G i) c
    · simp [buildRows, splitTail_ri]
    · simp [buildRows]
      exact dot_r0_ri rfl
  · intro hv
    rcases hv with ⟨hhead, htail, horth⟩
    have hri := succ_eq_ri_of_hasIsotropicHead_and_orthogonal_to_r0
      (K := K) x c v hhead horth
    rw [htail] at hri
    simpa [buildRows] using hri

theorem exists_unique_buildRows_succ_from_tail
    {m n : ℕ} (x : Fin n → K) (c : K) (G : Fin m → Fin n → K) (i : Fin m) :
    ∃! v : Fin (2 + n) → K,
      HasIsotropicHead (K := K) c v ∧
        splitTail (K := K) v = G i ∧
        dot (r0 x) v = 0 := by
  refine ⟨buildRows x c G (Fin.succ i), ?_, ?_⟩
  · exact (buildRows_succ_characterization (K := K) x c G i
      (buildRows x c G (Fin.succ i))).1 rfl
  · intro v hv
    exact (buildRows_succ_characterization (K := K) x c G i v).2 hv

theorem splitBuildFamily_iff_rebuild
    {m n : ℕ} {x : Fin n → K} {c : K}
    {R : Fin (m + 1) → Fin (2 + n) → K} :
    IsSplitBuildFamily (K := K) x c R ↔
      buildRows x c (deleteHyperbolicPairSplit (K := K) R) = R := by
  constructor
  · intro hR
    exact buildRows_deleteHyperbolicPairSplit_eq (K := K) hR
  · intro hR
    rw [← hR]
    exact buildRows_isSplitBuildFamily (K := K) x c
      (deleteHyperbolicPairSplit (K := K) R)

theorem buildRows_injective
    {m n : ℕ} (x : Fin n → K) (c : K) :
    Function.Injective (fun G : Fin m → Fin n → K => buildRows x c G) := by
  intro G H hGH
  have htail := congrArg (deleteHyperbolicPairSplit (K := K)) hGH
  simpa [deleteHyperbolicPairSplit_buildRows] using htail

theorem buildRows_eq_iff
    {m n : ℕ} (x : Fin n → K) (c : K)
    (G H : Fin m → Fin n → K) :
    buildRows x c G = buildRows x c H ↔ G = H := by
  constructor
  · intro h
    exact buildRows_injective (K := K) x c h
  · intro h
    rw [h]

theorem buildRows_linearIndependent_of_linearIndependent
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K))
    (hGlin : LinearIndependent K G) :
    LinearIndependent K (buildRows x c G) := by
  have hc0 : c ≠ 0 := by
    intro hzero
    have hneg1 : (-(1 : K)) ≠ 0 := by
      exact neg_ne_zero.mpr one_ne_zero
    have : (-(1 : K)) = 0 := by
      simpa [hzero] using hc.symm
    exact hneg1 this
  let S : Fin m → Fin (2 + n) → K := fun i => ri c (dot x (G i)) (G i)
  have hsuccLin : LinearIndependent K S := by
    have hcomp : (fun i => splitTailLinear (K := K) (S i)) = G := by
      funext i
      show splitTail (K := K) (S i) = G i
      simp [S, splitTail_ri]
    have hcompLin : LinearIndependent K (fun i => splitTailLinear (K := K) (S i)) := by
      convert hGlin using 1
    exact LinearIndependent.of_comp (splitTailLinear (K := K)) hcompLin
  have hnotmem : r0 x ∉ Submodule.span K (Set.range S) := by
    intro hmem
    have hhead :
        ∀ y ∈ Submodule.span K (Set.range S), y 1 = c * y 0 := by
      intro y hy
      refine Submodule.span_induction (p := fun z _ => z 1 = c * z 0) ?_ ?_ ?_ ?_ hy
      · intro z hz
        rcases hz with ⟨i, rfl⟩
        simp [S, ri, prepend2_apply_zero, prepend2_apply_one]
      · simp
      · intro y z hy hz hyEq hzEq
        calc
          (y + z) 1 = y 1 + z 1 := by simp [Pi.add_apply]
          _ = c * y 0 + c * z 0 := by rw [hyEq, hzEq]
          _ = c * ((y + z) 0) := by simp [Pi.add_apply, mul_add]
      · intro a y hy hyEq
        calc
          (a • y) 1 = a * y 1 := by simp [Pi.smul_apply]
          _ = a * (c * y 0) := by rw [hyEq]
          _ = c * (a * y 0) := by ring
          _ = c * ((a • y) 0) := by simp [Pi.smul_apply]
    have hprop := hhead (r0 x) hmem
    have : c = 0 := by
      simpa [r0, mul_one] using hprop.symm
    exact hc0 this
  simpa [S, buildRows] using LinearIndependent.fin_cons hsuccLin hnotmem

theorem buildRows_finrank_of_linearIndependent
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hlin : LinearIndependent K (buildRows x c G)) :
    Module.finrank K ↥(rowSpace (buildRows x c G)) = m + 1 := by
  let e : ↥(rowSpace (buildRows x c G)) ≃ₗ[K] (Fin (m + 1) →₀ K) :=
    LinearEquiv.ofBijective (hlin.repr)
      ⟨(LinearMap.ker_eq_bot.mp hlin.repr_ker),
        (LinearMap.range_eq_top.mp hlin.repr_range)⟩
  calc
    Module.finrank K ↥(rowSpace (buildRows x c G))
        = Module.finrank K (Fin (m + 1) →₀ K) := by
          exact LinearEquiv.finrank_eq e
    _ = Fintype.card (Fin (m + 1)) := by
          simp
    _ = m + 1 := by
          simp

theorem exists_unique_split_parent_of_IsSplitBuildFamily
    {m n : ℕ} {x : Fin n → K} {c : K}
    {R : Fin (m + 1) → Fin (2 + n) → K}
    (hR : IsSplitBuildFamily (K := K) x c R) :
    ∃! G : Fin m → Fin n → K, buildRows x c G = R := by
  refine ⟨deleteHyperbolicPairSplit (K := K) R, ?_, ?_⟩
  · exact buildRows_deleteHyperbolicPairSplit_eq (K := K) hR
  · intro G hG
    have htail := congrArg (deleteHyperbolicPairSplit (K := K)) hG
    simpa [deleteHyperbolicPairSplit_buildRows] using htail

theorem isSplitBuildFamily_iff_rowwise
    {m n : ℕ} {x : Fin n → K} {c : K}
    {R : Fin (m + 1) → Fin (2 + n) → K} :
    IsSplitBuildFamily (K := K) x c R ↔
      R 0 = r0 x ∧
      ∀ i : Fin m,
        R (Fin.succ i) =
          ri c (dot x (splitTail (K := K) (R (Fin.succ i))))
            (splitTail (K := K) (R (Fin.succ i))) := by
  constructor
  · intro hR
    rcases hR with ⟨h0, hs⟩
    refine ⟨h0, ?_⟩
    intro i
    rcases hs i with ⟨hhead, horth⟩
    exact succ_eq_ri_of_hasIsotropicHead_and_orthogonal_to_r0
      (K := K) x c (R (Fin.succ i)) hhead horth
  · intro hR
    rcases hR with ⟨h0, hs⟩
    refine ⟨h0, ?_⟩
    intro i
    refine ⟨?_, ?_⟩
    · rw [hs i]
      simpa using hasIsotropicHead_ri (K := K) x
        (splitTail (K := K) (R (Fin.succ i))) c
    · rw [hs i]
      exact dot_r0_ri rfl

theorem exists_unique_splitBuildFamily_of_parent
    {m n : ℕ} (x : Fin n → K) (c : K) (G : Fin m → Fin n → K) :
    ∃! R : Fin (m + 1) → Fin (2 + n) → K,
      IsSplitBuildFamily (K := K) x c R ∧
        deleteHyperbolicPairSplit (K := K) R = G := by
  refine ⟨buildRows x c G, ?_, ?_⟩
  · refine ⟨buildRows_isSplitBuildFamily (K := K) x c G, ?_⟩
    exact deleteHyperbolicPairSplit_buildRows (K := K) x c G
  · intro R hR
    rcases hR with ⟨hbuild, htail⟩
    have hrebuild := buildRows_deleteHyperbolicPairSplit_eq (K := K) hbuild
    rw [htail] at hrebuild
    exact hrebuild.symm

theorem buildRows_zero_zero
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hx : dot x x = (-1 : K)) :
    dot (buildRows x c G 0) (buildRows x c G 0) = 0 := by
  simp [buildRows]
  exact dot_r0_r0 hx

theorem buildRows_zero_succ
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K} (i : Fin m) :
    dot (buildRows x c G 0) (buildRows x c G (Fin.succ i)) = 0 := by
  simp [buildRows]
  exact dot_r0_ri rfl

theorem buildRows_succ_zero
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K} (i : Fin m) :
    dot (buildRows x c G (Fin.succ i)) (buildRows x c G 0) = 0 := by
  rw [dot_comm]
  exact buildRows_zero_succ i

theorem buildRows_succ_succ
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hc : c ^ 2 = (-1 : K))
    (hG : ∀ i j : Fin m, dot (G i) (G j) = 0)
    (i j : Fin m) :
    dot (buildRows x c G (Fin.succ i)) (buildRows x c G (Fin.succ j)) = 0 := by
  simp [buildRows]
  exact dot_ri_ri (hc := hc) (hgh := hG i j)

theorem buildRows_orthogonal
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hx : dot x x = (-1 : K))
    (hc : c ^ 2 = (-1 : K))
    (hG : ∀ i j : Fin m, dot (G i) (G j) = 0) :
    ∀ i j : Fin (m + 1), dot (buildRows x c G i) (buildRows x c G j) = 0 := by
  intro i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact buildRows_zero_zero hx
    · exact buildRows_zero_succ j
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact buildRows_succ_zero i
    · exact buildRows_succ_succ (hc := hc) (hG := hG) i j

theorem buildRows_pairwiseOrthogonal
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hx : dot x x = (-1 : K))
    (hc : c ^ 2 = (-1 : K))
    (hG : ∀ i j : Fin m, dot (G i) (G j) = 0) :
    PairwiseOrthogonal (K := K) (buildRows x c G) := by
  exact buildRows_orthogonal (hx := hx) (hc := hc) (hG := hG)

theorem buildRows_pairwiseOrthogonal_iff_gramZero
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K} :
    PairwiseOrthogonal (K := K) (buildRows x c G) ↔
      GramZero (K := K) (buildRows x c G) := by
  exact pairwiseOrthogonal_iff_gramZero (K := K) (R := buildRows x c G)

theorem buildRows_pairwiseOrthogonal_iff_rowSpace_le_orthogonal
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K} :
    PairwiseOrthogonal (K := K) (buildRows x c G) ↔
      rowSpace (buildRows x c G) ≤
        (dotBilin (K := K) (n := 2 + n)).orthogonal (rowSpace (buildRows x c G)) := by
  exact pairwiseOrthogonal_iff_rowSpace_le_orthogonal (K := K) (R := buildRows x c G)

theorem buildRows_gramZero_iff_rowSpace_le_orthogonal
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K} :
    GramZero (K := K) (buildRows x c G) ↔
      rowSpace (buildRows x c G) ≤
        (dotBilin (K := K) (n := 2 + n)).orthogonal (rowSpace (buildRows x c G)) := by
  rw [← buildRows_pairwiseOrthogonal_iff_gramZero (K := K) (x := x) (c := c) (G := G)]
  exact buildRows_pairwiseOrthogonal_iff_rowSpace_le_orthogonal
    (K := K) (x := x) (c := c) (G := G)

theorem buildRows_matrix_gram_zero
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hx : dot x x = (-1 : K))
    (hc : c ^ 2 = (-1 : K))
    (hG : ∀ i j : Fin m, dot (G i) (G j) = 0) :
    rowMatrix (buildRows x c G) * (rowMatrix (buildRows x c G)).transpose = 0 := by
  ext i j
  rw [rowMatrix_mul_transpose_apply]
  exact buildRows_orthogonal (hx := hx) (hc := hc) (hG := hG) i j

theorem buildRows_rowSpace_le_orthogonal
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hx : dot x x = (-1 : K))
    (hc : c ^ 2 = (-1 : K))
    (hG : ∀ i j : Fin m, dot (G i) (G j) = 0) :
    rowSpace (buildRows x c G) ≤
      (dotBilin (K := K) (n := 2 + n)).orthogonal (rowSpace (buildRows x c G)) := by
  apply rowSpace_le_orthogonal_of_pairwise_zero
  exact buildRows_orthogonal (hx := hx) (hc := hc) (hG := hG)

theorem buildRows_equivalent_conditions
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hx : dot x x = (-1 : K))
    (hc : c ^ 2 = (-1 : K))
    (hG : ∀ i j : Fin m, dot (G i) (G j) = 0) :
    PairwiseOrthogonal (K := K) (buildRows x c G) ∧
      GramZero (K := K) (buildRows x c G) ∧
      rowSpace (buildRows x c G) ≤
        (dotBilin (K := K) (n := 2 + n)).orthogonal (rowSpace (buildRows x c G)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact buildRows_pairwiseOrthogonal (K := K) (hx := hx) (hc := hc) (hG := hG)
  · exact (buildRows_pairwiseOrthogonal_iff_gramZero (K := K) (x := x) (c := c) (G := G)).1
      (buildRows_pairwiseOrthogonal (K := K) (hx := hx) (hc := hc) (hG := hG))
  · exact buildRows_rowSpace_le_orthogonal (K := K) (hx := hx) (hc := hc) (hG := hG)

theorem buildRows_rowSpace_self_dual_of_finrank_half
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hx : dot x x = (-1 : K))
    (hc : c ^ 2 = (-1 : K))
    (hG : ∀ i j : Fin m, dot (G i) (G j) = 0)
    (heven : Even n)
    (hdim : Module.finrank K ↥(rowSpace (buildRows x c G)) = (n + 2) / 2) :
    rowSpace (buildRows x c G) =
      (dotBilin (K := K) (n := 2 + n)).orthogonal (rowSpace (buildRows x c G)) := by
  let C := rowSpace (buildRows x c G)
  let B := dotBilin (K := K) (n := 2 + n)
  have hle : C ≤ B.orthogonal C := by
    exact buildRows_rowSpace_le_orthogonal (hx := hx) (hc := hc) (hG := hG)
  have hadd :
      Module.finrank K ↥C + Module.finrank K ↥(B.orthogonal C) =
        Module.finrank K (Fin (2 + n) → K) +
          Module.finrank K ↥(C ⊓ B.orthogonal ⊤) := by
    simpa [B, C] using
      (LinearMap.BilinForm.finrank_add_finrank_orthogonal
        (B := B) (dotBilin_isRefl (K := K) (n := 2 + n)) C)
  have htop : B.orthogonal ⊤ = ⊥ := by
    rw [LinearMap.BilinForm.orthogonal_top_eq_ker
      (B := B) (dotBilin_isRefl (K := K) (n := 2 + n))]
    exact (dotBilin_nondegenerate (K := K) (n := 2 + n)).ker_eq_bot
  have hfinOrth : Module.finrank K ↥(B.orthogonal C) = (n + 2) / 2 := by
    have hbotfin :
        Module.finrank K ↥((⊥ : Submodule K (Fin (2 + n) → K))) = 0 := by
      simp
    have hcalc :
        Module.finrank K ↥C + Module.finrank K ↥(B.orthogonal C) = n + 2 := by
      have hcalc' := hadd
      rw [htop, inf_bot_eq, hbotfin, add_zero,
        Module.finrank_fintype_fun_eq_card (R := K) (η := Fin (2 + n)), Fintype.card_fin] at hcalc'
      simpa [Nat.add_comm] using hcalc'
    rcases heven with ⟨k, rfl⟩
    have hhalf : (k + k) / 2 + 1 = k + 1 := by
      omega
    have hdim' : Module.finrank K ↥C = k + 1 := by
      simpa [C, hhalf] using hdim
    have hcalc' :
        Module.finrank K ↥C + Module.finrank K ↥(B.orthogonal C) = k + (k + 2) := by
      simpa [Nat.add_assoc] using hcalc
    omega
  apply Submodule.eq_of_le_of_finrank_eq hle
  exact hdim.trans hfinOrth.symm

theorem buildRows_rowSpace_self_dual_of_self_dual_parent_basis
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hx : dot x x = (-1 : K))
    (hc : c ^ 2 = (-1 : K))
    (hGorth : ∀ i j : Fin m, dot (G i) (G j) = 0)
    (hGlin : LinearIndependent K G)
    (heven : Even n)
    (hcard : m + 1 = (n + 2) / 2) :
    rowSpace (buildRows x c G) =
      (dotBilin (K := K) (n := 2 + n)).orthogonal
        (rowSpace (buildRows x c G)) := by
  have hbuildLin : LinearIndependent K (buildRows x c G) :=
    buildRows_linearIndependent_of_linearIndependent (K := K) hc hGlin
  have hdim :
      Module.finrank K ↥(rowSpace (buildRows x c G)) = (n + 2) / 2 := by
    rw [buildRows_finrank_of_linearIndependent (K := K) hbuildLin]
    exact hcard
  exact buildRows_rowSpace_self_dual_of_finrank_half
    (K := K) (hx := hx) (hc := hc) (hG := hGorth) (heven := heven) (hdim := hdim)

end SplitBuildingUp

section BinaryBoxedReduction

variable {K : Type*} [Field K]

def riBin {n : ℕ} (yi : K) (g : Fin n → K) : Fin (2 + n) → K :=
  prepend2 yi yi g

/-- A boxed-reduction family with explicit coefficients `Y i`. -/
def boxedFamily {m n : ℕ}
    (x : Fin n → K) (Y : Fin m → K) (G : Fin m → Fin n → K) :
    Fin (m + 1) → Fin (2 + n) → K :=
  Fin.cases (r0 x) (fun i => riBin (Y i) (G i))

/-- The Kim building-up family, where the coefficient is `dot x (G i)`. -/
def buildRowsBin {m n : ℕ}
    (x : Fin n → K) (G : Fin m → Fin n → K) :
    Fin (m + 1) → Fin (2 + n) → K :=
  Fin.cases (r0 x) (fun i => riBin (dot x (G i)) (G i))

theorem boxedFamily_eq_buildRowsBin
    {m n : ℕ}
    {x : Fin n → K} {Y : Fin m → K} {G : Fin m → Fin n → K}
    (hY : ∀ i : Fin m, Y i = dot x (G i)) :
    boxedFamily x Y G = buildRowsBin x G := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [boxedFamily, buildRowsBin]
  · simp [boxedFamily, buildRowsBin, hY j]

def tailVec {n : ℕ} (v : Fin (2 + n) → K) : Fin n → K :=
  fun j => v (Fin.natAdd 2 j)

def deleteHyperbolicPair {m n : ℕ}
    (R : Fin (m + 1) → Fin (2 + n) → K) : Fin m → Fin n → K :=
  fun i => tailVec (R (Fin.succ i))

theorem tailVec_prepend2
    {n : ℕ} (a b : K) (u : Fin n → K) :
    tailVec (prepend2 a b u) = u := by
  funext j
  simp [tailVec, prepend2]

theorem tailVec_r0
    {n : ℕ} (x : Fin n → K) :
    tailVec (r0 x) = x := by
  simpa [r0] using tailVec_prepend2 (K := K) 1 0 x

theorem tailVec_riBin
    {n : ℕ} (yi : K) (g : Fin n → K) :
    tailVec (riBin yi g) = g := by
  simpa [riBin] using tailVec_prepend2 (K := K) yi yi g

theorem buildRowsBin_zero
    {m n : ℕ} (x : Fin n → K) (G : Fin m → Fin n → K) :
    buildRowsBin x G 0 = r0 x := by
  simp [buildRowsBin]

theorem buildRowsBin_succ
    {m n : ℕ} (x : Fin n → K) (G : Fin m → Fin n → K) (i : Fin m) :
    buildRowsBin x G (Fin.succ i) = riBin (dot x (G i)) (G i) := by
  simp [buildRowsBin]

theorem deleteHyperbolicPair_buildRowsBin
    {m n : ℕ} (x : Fin n → K) (G : Fin m → Fin n → K) :
    deleteHyperbolicPair (buildRowsBin x G) = G := by
  funext i
  funext j
  rw [deleteHyperbolicPair]
  simp [tailVec, buildRowsBin, riBin, prepend2]

theorem buildRowsBin_deleteHyperbolicPair_eq
    {m n : ℕ} {x : Fin n → K} {R : Fin (m + 1) → Fin (2 + n) → K}
    (h0 : R 0 = r0 x)
    (hs : ∀ i : Fin m,
      R (Fin.succ i) = riBin (dot x (tailVec (R (Fin.succ i)))) (tailVec (R (Fin.succ i)))) :
    buildRowsBin x (deleteHyperbolicPair R) = R := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  ·
    rw [buildRowsBin_zero]
    exact h0.symm
  ·
    rw [buildRowsBin_succ]
    change
      riBin (dot x (tailVec (R (Fin.succ j)))) (tailVec (R (Fin.succ j))) =
        R (Fin.succ j)
    exact (hs j).symm

def IsBoxedKimFamily {m n : ℕ}
    (x : Fin n → K) (R : Fin (m + 1) → Fin (2 + n) → K) : Prop :=
  R 0 = r0 x ∧
  ∀ i : Fin m,
    R (Fin.succ i) =
      riBin (dot x (tailVec (R (Fin.succ i)))) (tailVec (R (Fin.succ i)))

theorem rebuild_of_IsBoxedKimFamily
    {m n : ℕ} {x : Fin n → K} {R : Fin (m + 1) → Fin (2 + n) → K}
    (hR : IsBoxedKimFamily x R) :
    buildRowsBin x (deleteHyperbolicPair R) = R := by
  rcases hR with ⟨h0, hs⟩
  exact buildRowsBin_deleteHyperbolicPair_eq h0 hs

def permuteVec {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → K) : Fin n → K :=
  fun j => v (σ j)

def permuteFamily {m n : ℕ} (σ : Equiv.Perm (Fin n)) (R : Fin m → Fin n → K) :
    Fin m → Fin n → K :=
  fun i => permuteVec σ (R i)

def SameCode {m₁ m₂ n : ℕ}
    (R : Fin m₁ → Fin n → K) (S : Fin m₂ → Fin n → K) : Prop :=
  rowSpace R = rowSpace S

def CodeEquiv {m₁ m₂ n : ℕ}
    (R : Fin m₁ → Fin n → K) (S : Fin m₂ → Fin n → K) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), SameCode (permuteFamily σ R) S

def linearEquivFamily {m n n' : ℕ}
    (e : (Fin n → K) ≃ₗ[K] (Fin n' → K)) (R : Fin m → Fin n → K) :
    Fin m → Fin n' → K :=
  fun i => e (R i)

def AmbientLinearCodeEquiv {m₁ m₂ n : ℕ}
    (R : Fin m₁ → Fin n → K) (S : Fin m₂ → Fin n → K) : Prop :=
  ∃ e : (Fin n → K) ≃ₗ[K] (Fin n → K), SameCode (linearEquivFamily e R) S

def rowScaleFamily {m n : ℕ} (a : Fin m → K) (R : Fin m → Fin n → K) :
    Fin m → Fin n → K :=
  fun i => a i • R i

def reindexFamily {m n : ℕ} (σ : Equiv.Perm (Fin m)) (R : Fin m → Fin n → K) :
    Fin m → Fin n → K :=
  fun i => R (σ i)

def pivotNormalizeScales {m : ℕ} (a : K) : Fin (m + 1) → K :=
  fun i => if i = 0 then a⁻¹ else 1

def pivotNormalizeFamily {m n : ℕ}
    (i₀ : Fin (m + 1)) (a : K) (R : Fin (m + 1) → Fin n → K) :
    Fin (m + 1) → Fin n → K :=
  rowScaleFamily (pivotNormalizeScales (m := m) a)
    (reindexFamily (Equiv.swap 0 i₀) R)

theorem permuteVec_refl {n : ℕ} (v : Fin n → K) :
    permuteVec (Equiv.refl (Fin n)) v = v := by
  funext j
  rfl

theorem permuteFamily_refl {m n : ℕ} (R : Fin m → Fin n → K) :
    permuteFamily (Equiv.refl (Fin n)) R = R := by
  funext i
  exact permuteVec_refl (R i)

theorem sameCode_refl {m n : ℕ} (R : Fin m → Fin n → K) : SameCode R R := rfl

theorem sameCode_symm
    {m₁ m₂ n : ℕ} {R : Fin m₁ → Fin n → K} {S : Fin m₂ → Fin n → K}
    (h : SameCode R S) : SameCode S R := h.symm

theorem sameCode_trans
    {m₁ m₂ m₃ n : ℕ}
    {R : Fin m₁ → Fin n → K} {S : Fin m₂ → Fin n → K} {T : Fin m₃ → Fin n → K}
    (hRS : SameCode R S) (hST : SameCode S T) : SameCode R T :=
  hRS.trans hST

theorem sameCode_of_eq
    {m n : ℕ} {R S : Fin m → Fin n → K} (h : R = S) :
    SameCode R S := by
  cases h
  rfl

theorem rowSpace_linearEquivFamily_eq_map
    {m n n' : ℕ}
    (e : (Fin n → K) ≃ₗ[K] (Fin n' → K)) (R : Fin m → Fin n → K) :
    rowSpace (linearEquivFamily e R) = Submodule.map e.toLinearMap (rowSpace R) := by
  apply le_antisymm
  · rw [rowSpace]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨R i, mem_rowSpace R i, rfl⟩
  · rintro x hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [rowSpace] at hy
    refine Submodule.span_induction
        (p := fun z _ => e z ∈ rowSpace (linearEquivFamily e R))
        ?_ ?_ ?_ ?_ hy
    · intro z hz
      rcases hz with ⟨i, rfl⟩
      exact mem_rowSpace (linearEquivFamily e R) i
    · simpa using (Submodule.zero_mem (rowSpace (linearEquivFamily e R)))
    · intro u v hu hv hu' hv'
      simpa using Submodule.add_mem (rowSpace (linearEquivFamily e R)) hu' hv'
    · intro a u hu hu'
      simpa using Submodule.smul_mem (rowSpace (linearEquivFamily e R)) a hu'

theorem sameCode_linearEquivFamily
    {m₁ m₂ n n' : ℕ}
    (e : (Fin n → K) ≃ₗ[K] (Fin n' → K))
    {R : Fin m₁ → Fin n → K} {S : Fin m₂ → Fin n → K}
    (h : SameCode R S) :
    SameCode (linearEquivFamily e R) (linearEquivFamily e S) := by
  rw [SameCode] at h ⊢
  simpa [rowSpace_linearEquivFamily_eq_map] using congrArg (Submodule.map e.toLinearMap) h

theorem pivotPureTailRows_head_relation
    {m n : ℕ} (x : Fin n → K) (c : K) (a : Fin m → K) (G : Fin m → Fin n → K)
    (i : Fin (m + 1)) :
    pivotPureTailRows x c a G i 1 = c * pivotPureTailRows x c a G i 0 := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [pivotPureTailRows]
  · simp [pivotPureTailRows]

theorem mem_rowSpace_pivotPureTailRows_head_relation
    {m n : ℕ} (x : Fin n → K) (c : K) (a : Fin m → K) (G : Fin m → Fin n → K)
    {v : Fin (2 + n) → K}
    (hv : v ∈ rowSpace (pivotPureTailRows x c a G)) :
    v 1 = c * v 0 := by
  rw [rowSpace] at hv
  refine Submodule.span_induction
      (p := fun z _ => z 1 = c * z 0)
      ?_ ?_ ?_ ?_ hv
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    exact pivotPureTailRows_head_relation (K := K) x c a G i
  · simp
  · intro u w hu hw hu0 hw0
    rw [Pi.add_apply, Pi.add_apply, hu0, hw0]
    ring
  · intro b u hu hu0
    rw [Pi.smul_apply, Pi.smul_apply, hu0]
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

theorem r0_not_mem_rowSpace_pivotPureTailRows
    {m n : ℕ} (x y : Fin n → K) (c : K) (a : Fin m → K) (G : Fin m → Fin n → K)
    (hc : c ^ 2 = (-1 : K)) :
    r0 y ∉ rowSpace (pivotPureTailRows x c a G) := by
  intro hr0
  have hhead :
      r0 y 1 = c * r0 y 0 :=
    mem_rowSpace_pivotPureTailRows_head_relation (K := K) x c a G hr0
  have hzero : (0 : K) = c := by
    simpa [r0] using hhead
  exact (root_neg_one_ne_zero (K := K) hc) hzero.symm

theorem not_sameCode_buildRows_pivotPureTailRows
    {m n : ℕ} (x y : Fin n → K) (c : K)
    (a : Fin m → K) (G H : Fin m → Fin n → K)
    (hc : c ^ 2 = (-1 : K)) :
    ¬ SameCode (buildRows y c H) (pivotPureTailRows x c a G) := by
  intro hSame
  have hr0build : r0 y ∈ rowSpace (buildRows y c H) :=
    mem_rowSpace (buildRows y c H) 0
  have hr0pure : r0 y ∈ rowSpace (pivotPureTailRows x c a G) := by
    rw [← hSame]
    exact hr0build
  exact r0_not_mem_rowSpace_pivotPureTailRows (K := K) x y c a G hc hr0pure

theorem not_sameCode_pivotPureTailRows_buildRows
    {m n : ℕ} (x y : Fin n → K) (c : K)
    (a : Fin m → K) (G H : Fin m → Fin n → K)
    (hc : c ^ 2 = (-1 : K)) :
    ¬ SameCode (pivotPureTailRows x c a G) (buildRows y c H) := by
  intro hSame
  exact not_sameCode_buildRows_pivotPureTailRows
    (K := K) x y c a G H hc (sameCode_symm hSame)

theorem sameCode_pivotRows_pivotPureTailRows
    {m n : ℕ} (x : Fin n → K) (c : K) (a : Fin m → K) (G : Fin m → Fin n → K) :
    SameCode (pivotRows x c a G) (pivotPureTailRows x c a G) := by
  apply le_antisymm
  · rw [rowSpace]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact mem_rowSpace _ 0
    · rw [pivotRows_succ_eq_smul_zero_add_pureTail (K := K) x c a G j]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (mem_rowSpace _ 0))
        (mem_rowSpace _ (Fin.succ j))
  · rw [rowSpace]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact mem_rowSpace _ 0
    · rw [pivotPureTailRows_succ_eq_sub_smul_zero (K := K) x c a G j]
      exact Submodule.sub_mem _ (mem_rowSpace _ (Fin.succ j))
        (Submodule.smul_mem _ _ (mem_rowSpace _ 0))

theorem rowSpace_rowScaleFamily_eq
    {m n : ℕ} (a : Fin m → K) (R : Fin m → Fin n → K)
    (ha : ∀ i : Fin m, a i ≠ 0) :
    rowSpace (rowScaleFamily a R) = rowSpace R := by
  apply le_antisymm
  · rw [rowSpace]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    change a i • R i ∈ rowSpace R
    exact Submodule.smul_mem _ _ (mem_rowSpace R i)
  · rw [rowSpace]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    have hscaled : rowScaleFamily a R i ∈ rowSpace (rowScaleFamily a R) :=
      mem_rowSpace (rowScaleFamily a R) i
    change R i ∈ rowSpace (rowScaleFamily a R)
    have hEq : R i = (a i)⁻¹ • rowScaleFamily a R i := by
      simp [rowScaleFamily, Pi.smul_apply, smul_eq_mul, ha i, mul_assoc]
    rw [hEq]
    exact Submodule.smul_mem _ _ hscaled

theorem sameCode_rowScaleFamily
    {m n : ℕ} (a : Fin m → K) (R : Fin m → Fin n → K)
    (ha : ∀ i : Fin m, a i ≠ 0) :
    SameCode (rowScaleFamily a R) R := by
  exact rowSpace_rowScaleFamily_eq a R ha

theorem rowSpace_reindexFamily_eq
    {m n : ℕ} (σ : Equiv.Perm (Fin m)) (R : Fin m → Fin n → K) :
    rowSpace (reindexFamily σ R) = rowSpace R := by
  apply le_antisymm
  · rw [rowSpace]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    change R (σ i) ∈ rowSpace R
    exact mem_rowSpace R (σ i)
  · rw [rowSpace]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    have hreindexed : reindexFamily σ R (σ⁻¹ i) ∈ rowSpace (reindexFamily σ R) :=
      mem_rowSpace (reindexFamily σ R) (σ⁻¹ i)
    simpa [reindexFamily] using hreindexed

theorem sameCode_reindexFamily
    {m n : ℕ} (σ : Equiv.Perm (Fin m)) (R : Fin m → Fin n → K) :
    SameCode (reindexFamily σ R) R := by
  exact rowSpace_reindexFamily_eq σ R

theorem pairwiseOrthogonal_rowScaleFamily
    {m n : ℕ} (a : Fin m → K) (R : Fin m → Fin n → K)
    (ha : ∀ i : Fin m, a i ≠ 0)
    (hR : PairwiseOrthogonal (K := K) R) :
    PairwiseOrthogonal (K := K) (rowScaleFamily a R) := by
  intro i j
  rw [rowScaleFamily, rowScaleFamily, dot_smul_left, dot_smul_right, hR i j]
  simp

theorem pairwiseOrthogonal_reindexFamily
    {m n : ℕ} (σ : Equiv.Perm (Fin m)) (R : Fin m → Fin n → K)
    (hR : PairwiseOrthogonal (K := K) R) :
    PairwiseOrthogonal (K := K) (reindexFamily σ R) := by
  intro i j
  simpa [reindexFamily] using hR (σ i) (σ j)

theorem sameCode_pivotNormalizeFamily
    {m n : ℕ} (i₀ : Fin (m + 1)) (a : K) (R : Fin (m + 1) → Fin n → K)
    (ha : a ≠ 0) :
    SameCode (pivotNormalizeFamily i₀ a R) R := by
  apply sameCode_trans
  · exact sameCode_rowScaleFamily (a := pivotNormalizeScales (m := m) a)
      (R := reindexFamily (Equiv.swap 0 i₀) R) (ha := by
        intro i
        by_cases h : i = 0
        · simp [pivotNormalizeScales, h, ha]
        · simp [pivotNormalizeScales, h])
  · exact sameCode_reindexFamily (σ := Equiv.swap 0 i₀) (R := R)

theorem pairwiseOrthogonal_pivotNormalizeFamily
    {m n : ℕ} (i₀ : Fin (m + 1)) (a : K) (R : Fin (m + 1) → Fin n → K)
    (ha : a ≠ 0)
    (hR : PairwiseOrthogonal (K := K) R) :
    PairwiseOrthogonal (K := K) (pivotNormalizeFamily i₀ a R) := by
  apply pairwiseOrthogonal_rowScaleFamily (K := K)
    (a := pivotNormalizeScales (m := m) a)
    (R := reindexFamily (Equiv.swap 0 i₀) R)
  · intro i
    by_cases h : i = 0
    · simp [pivotNormalizeScales, h, ha]
    · simp [pivotNormalizeScales, h]
  · exact pairwiseOrthogonal_reindexFamily (K := K)
      (σ := Equiv.swap 0 i₀) (R := R) hR

theorem inv_smul_prepend2_on_isotropic_line
    {n : ℕ} {a c : K} (ha : a ≠ 0) (g : Fin n → K) :
    a⁻¹ • prepend2 a (c * a) g = prepend2 1 c ((a⁻¹) • g) := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    fin_cases k
    · simp [prepend2, head2, Pi.smul_apply, smul_eq_mul, ha]
    · simp [prepend2, head2, Pi.smul_apply, smul_eq_mul, ha, mul_assoc, mul_left_comm, mul_comm]
  · intro k
    simp [prepend2, head2, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem pivotNormalizeFamily_zero
    {m n : ℕ} (i₀ : Fin (m + 1)) (a : K) (R : Fin (m + 1) → Fin n → K) :
    pivotNormalizeFamily i₀ a R 0 = a⁻¹ • R i₀ := by
  simp [pivotNormalizeFamily, pivotNormalizeScales, rowScaleFamily, reindexFamily]

theorem pivotNormalizeFamily_zero_prepend2_on_isotropic_line
    {m n : ℕ} (i₀ : Fin (m + 1)) {a c : K} (R : Fin (m + 1) → Fin (2 + n) → K)
    (g : Fin n → K) (ha : a ≠ 0)
    (hrow : R i₀ = prepend2 a (c * a) g) :
    pivotNormalizeFamily i₀ a R 0 = prepend2 1 c ((a⁻¹) • g) := by
  rw [pivotNormalizeFamily_zero, hrow]
  exact inv_smul_prepend2_on_isotropic_line (K := K) ha g

theorem pivotNormalizeFamily_succ
    {m n : ℕ} (i₀ : Fin (m + 1)) (a : K) (R : Fin (m + 1) → Fin n → K)
    (i : Fin m) :
    pivotNormalizeFamily i₀ a R (Fin.succ i) =
      R ((Equiv.swap 0 i₀) (Fin.succ i)) := by
  simp [pivotNormalizeFamily, pivotNormalizeScales, rowScaleFamily, reindexFamily]

theorem pivotNormalizeFamily_isPivotNormalizedFamily
    {m n : ℕ} (i₀ : Fin (m + 1)) {a c : K}
    (R : Fin (m + 1) → Fin (2 + n) → K)
    (g : Fin n → K) (ha : a ≠ 0)
    (hrow : R i₀ = prepend2 a (c * a) g)
    (hall : ∀ j : Fin (m + 1), HasIsotropicHead (K := K) c (R j)) :
    IsPivotNormalizedFamily (K := K) ((a⁻¹) • g) c
      (pivotNormalizeFamily i₀ a R) := by
  constructor
  · exact pivotNormalizeFamily_zero_prepend2_on_isotropic_line
      (K := K) i₀ R g ha hrow
  · intro i
    rcases hall ((Equiv.swap 0 i₀) (Fin.succ i)) with ⟨b, h, hh⟩
    refine ⟨b, h, ?_⟩
    rw [pivotNormalizeFamily_succ (K := K) i₀ a R i]
    exact hh

theorem pivotNormalizeFamily_deleteHyperbolicPairSplit_isPivotTailFamily
    {m n : ℕ} (i₀ : Fin (m + 1)) {a c : K}
    (R : Fin (m + 1) → Fin (2 + n) → K)
    (g : Fin n → K) (ha : a ≠ 0)
    (hc : c ^ 2 = (-1 : K))
    (hrow : R i₀ = prepend2 a (c * a) g)
    (hall : ∀ j : Fin (m + 1), HasIsotropicHead (K := K) c (R j))
    (horth : PairwiseOrthogonal (K := K) R) :
    IsPivotTailFamily (K := K) ((a⁻¹) • g)
      (deleteHyperbolicPairSplit (K := K) (pivotNormalizeFamily i₀ a R)) := by
  have hnorm : IsPivotNormalizedFamily (K := K) ((a⁻¹) • g) c
      (pivotNormalizeFamily i₀ a R) :=
    pivotNormalizeFamily_isPivotNormalizedFamily
      (K := K) i₀ R g ha hrow hall
  have horth' : PairwiseOrthogonal (K := K) (pivotNormalizeFamily i₀ a R) :=
    pairwiseOrthogonal_pivotNormalizeFamily (K := K) i₀ a R ha horth
  exact pivotNormalizedFamily_deleteHyperbolicPairSplit_isPivotTailFamily
    (K := K) (x := (a⁻¹) • g) (c := c) (R := pivotNormalizeFamily i₀ a R)
    hc hnorm horth'

theorem exists_pivotNormalizedFamily_sameCode_and_isPivotTailFamily
    {m n : ℕ} (i₀ : Fin (m + 1)) {a c : K}
    (R : Fin (m + 1) → Fin (2 + n) → K)
    (g : Fin n → K) (ha : a ≠ 0)
    (hc : c ^ 2 = (-1 : K))
    (hrow : R i₀ = prepend2 a (c * a) g)
    (hall : ∀ j : Fin (m + 1), HasIsotropicHead (K := K) c (R j))
    (horth : PairwiseOrthogonal (K := K) R) :
    ∃ R' : Fin (m + 1) → Fin (2 + n) → K,
      SameCode R' R ∧
      IsPivotNormalizedFamily (K := K) ((a⁻¹) • g) c R' ∧
      PairwiseOrthogonal (K := K) R' ∧
      IsPivotTailFamily (K := K) ((a⁻¹) • g)
        (deleteHyperbolicPairSplit (K := K) R') := by
  refine ⟨pivotNormalizeFamily i₀ a R, ?_, ?_, ?_, ?_⟩
  · exact sameCode_pivotNormalizeFamily (K := K) i₀ a R ha
  · exact pivotNormalizeFamily_isPivotNormalizedFamily
      (K := K) i₀ R g ha hrow hall
  · exact pairwiseOrthogonal_pivotNormalizeFamily (K := K) i₀ a R ha horth
  · exact pivotNormalizeFamily_deleteHyperbolicPairSplit_isPivotTailFamily
      (K := K) i₀ R g ha hc hrow hall horth

theorem exists_pivotRows_sameCode_and_isPivotTailFamily
    {m n : ℕ} (i₀ : Fin (m + 1)) {a c : K}
    (R : Fin (m + 1) → Fin (2 + n) → K)
    (g : Fin n → K) (ha : a ≠ 0)
    (hc : c ^ 2 = (-1 : K))
    (hrow : R i₀ = prepend2 a (c * a) g)
    (hall : ∀ j : Fin (m + 1), HasIsotropicHead (K := K) c (R j))
    (horth : PairwiseOrthogonal (K := K) R) :
    ∃ x : Fin n → K, ∃ a' : Fin m → K, ∃ G : Fin m → Fin n → K,
      SameCode (pivotRows x c a' G) R ∧
      PairwiseOrthogonal (K := K) (pivotRows x c a' G) ∧
      IsPivotTailFamily (K := K) x G := by
  rcases exists_pivotNormalizedFamily_sameCode_and_isPivotTailFamily
      (K := K) i₀ R g ha hc hrow hall horth with
    ⟨R', hcode, hnorm, horth', htail⟩
  rcases exists_pivotRows_eq_of_IsPivotNormalizedFamily (K := K) hnorm with
    ⟨a', G, hEq⟩
  refine ⟨(a⁻¹) • g, a', G, ?_, ?_, ?_⟩
  · simpa [hEq] using hcode
  · simpa [hEq] using horth'
  · simpa [hEq,
      deleteHyperbolicPairSplit_pivotRows (K := K) ((a⁻¹) • g) c a' G] using htail

theorem exists_pivotPureTailRows_sameCode_and_isOrthogonalTailFamily
    {m n : ℕ} (i₀ : Fin (m + 1)) {a c : K}
    (R : Fin (m + 1) → Fin (2 + n) → K)
    (g : Fin n → K) (ha : a ≠ 0)
    (hc : c ^ 2 = (-1 : K))
    (hrow : R i₀ = prepend2 a (c * a) g)
    (hall : ∀ j : Fin (m + 1), HasIsotropicHead (K := K) c (R j))
    (horth : PairwiseOrthogonal (K := K) R) :
    ∃ x : Fin n → K, ∃ a' : Fin m → K, ∃ G : Fin m → Fin n → K,
      SameCode (pivotPureTailRows x c a' G) R ∧
      PairwiseOrthogonal (K := K) (pivotPureTailRows x c a' G) ∧
      IsOrthogonalTailFamily (K := K) x
        (deleteHyperbolicPairSplit (K := K) (pivotPureTailRows x c a' G)) := by
  rcases exists_pivotRows_sameCode_and_isPivotTailFamily
      (K := K) i₀ R g ha hc hrow hall horth with
    ⟨x, a', G, hcode, hpivot, htail⟩
  refine ⟨x, a', G, ?_, ?_, ?_⟩
  · exact sameCode_trans
      (sameCode_symm (sameCode_pivotRows_pivotPureTailRows (K := K) x c a' G)) hcode
  · exact pivotPureTailRows_pairwiseOrthogonal (K := K) hc htail
  · simpa [deleteHyperbolicPairSplit_pivotPureTailRows (K := K) x c a' G] using
      (pivotResidualTails_isOrthogonalTailFamily (K := K) (a := a') htail)

def HeadAlignCodeEquiv {m₁ m₂ n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (R : Fin m₁ → Fin (2 + n) → K) (S : Fin m₂ → Fin (2 + n) → K) : Prop :=
  rowSpace (headAlignFamily (K := K) c R) = rowSpace S

def splitDot {n : ℕ} (u v : Fin (2 + n) → K) : K :=
  (2 : K) * (u 0 * v 1 + u 1 * v 0) + dot (splitTail (K := K) u) (splitTail (K := K) v)

theorem splitDot_prepend2_prepend2
    {n : ℕ} (a b a' b' : K) (u v : Fin n → K) :
    splitDot (K := K) (prepend2 a b u) (prepend2 a' b' v) =
      (2 : K) * (a * b' + b * a') + dot u v := by
  simp [splitDot, splitTail_prepend2]

theorem splitDot_headAlignFamilyVec
    {n : ℕ} [Fact ((2 : K) ≠ 0)] {c : K}
    (hc : c ^ 2 = (-1 : K))
    (u v : Fin (2 + n) → K) :
    splitDot (K := K)
        (headAlignFamilyVec (K := K) c u)
        (headAlignFamilyVec (K := K) c v) =
      dot u v := by
  rw [headAlignFamilyVec, headAlignFamilyVec, splitDot_prepend2_prepend2 (K := K)]
  have h2 : (2 : K) ≠ 0 := Fact.out
  have hhead :
      (2 : K) *
          (((u 0 - c * u 1) / 2) * ((v 0 + c * v 1) / 2) +
            ((u 0 + c * u 1) / 2) * ((v 0 - c * v 1) / 2))
        = u 0 * v 0 + u 1 * v 1 := by
    have htmp :
        (((u 0 - c * u 1) / 2) * ((v 0 + c * v 1) / 2) +
            ((u 0 + c * u 1) / 2) * ((v 0 - c * v 1) / 2)) =
          (u 0 * v 0 + u 1 * v 1) / 2 := by
      have hc' : c * c = (-1 : K) := by
        simpa [pow_two] using hc
      apply (eq_div_iff h2).2
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      field_simp [h2]
      calc
        (u 0 - c * u 1) * (v 0 + c * v 1) + (u 0 + c * u 1) * (v 0 - c * v 1)
            = (2 : K) * (u 0 * v 0) - (2 : K) * (c * c) * (u 1 * v 1) := by
                ring
        _ = (2 : K) * (u 0 * v 0) - (2 : K) * (-1 : K) * (u 1 * v 1) := by
              rw [hc']
        _ = (2 : K) * (u 0 * v 0 + u 1 * v 1) := by
              ring
    calc
      (2 : K) *
          (((u 0 - c * u 1) / 2) * ((v 0 + c * v 1) / 2) +
            ((u 0 + c * u 1) / 2) * ((v 0 - c * v 1) / 2))
          = (2 : K) * ((u 0 * v 0 + u 1 * v 1) / 2) := by rw [htmp]
      _ = u 0 * v 0 + u 1 * v 1 := by
        simp [div_eq_mul_inv, h2, mul_assoc, mul_left_comm, mul_comm]
  rw [hhead]
  simpa [prepend2_head_splitTail] using
    (dot_prepend2_prepend2 (K := K) (u 0) (u 1) (v 0) (v 1)
      (splitTail (K := K) u) (splitTail (K := K) v)).symm

theorem dot_headUnalignFamilyVec
    {n : ℕ} {c : K}
    (hc : c ^ 2 = (-1 : K))
    (u v : Fin (2 + n) → K) :
    dot (headUnalignFamilyVec (K := K) c u) (headUnalignFamilyVec (K := K) c v) =
      splitDot (K := K) u v := by
  rw [headUnalignFamilyVec, headUnalignFamilyVec, dot_prepend2_prepend2]
  rw [splitDot]
  have hc' : c * c = (-1 : K) := by
    simpa [pow_two] using hc
  calc
    (u 0 + u 1) * (v 0 + v 1) + c * (u 0 - u 1) * (c * (v 0 - v 1)) +
        dot (splitTail (K := K) u) (splitTail (K := K) v)
      = (u 0 + u 1) * (v 0 + v 1) + (c * c) * ((u 0 - u 1) * (v 0 - v 1)) +
          dot (splitTail (K := K) u) (splitTail (K := K) v) := by
            ring
    _ = (u 0 + u 1) * (v 0 + v 1) + (-1 : K) * ((u 0 - u 1) * (v 0 - v 1)) +
          dot (splitTail (K := K) u) (splitTail (K := K) v) := by
            rw [hc']
    _ = splitDot (K := K) u v := by
          rw [splitDot]
          ring

structure IsHeadAlignmentWitness {n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (e : (Fin (2 + n) → K) ≃ₗ[K] (Fin (2 + n) → K)) : Prop where
  tail_eq : ∀ v : Fin (2 + n) → K,
    splitTail (K := K) (e v) = splitTail (K := K) v
  pivot_eq : ∀ x : Fin n → K, e (prepend2 1 c x) = r0 x
  zeroHead_eq : ∀ g : Fin n → K, e (prepend2 0 0 g) = prepend2 0 0 g

structure IsSplitIsometryWitness {n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (e : (Fin (2 + n) → K) ≃ₗ[K] (Fin (2 + n) → K)) : Prop where
  head : IsHeadAlignmentWitness (K := K) c e
  form_eq : ∀ u v : Fin (2 + n) → K,
    splitDot (K := K) (e u) (e v) = dot u v

def HeadAlignmentCodeEquiv {m₁ m₂ n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (R : Fin m₁ → Fin (2 + n) → K) (S : Fin m₂ → Fin (2 + n) → K) : Prop :=
  ∃ e : (Fin (2 + n) → K) ≃ₗ[K] (Fin (2 + n) → K),
    IsHeadAlignmentWitness (K := K) c e ∧
    SameCode (linearEquivFamily e R) S

def SplitIsometryCodeEquiv {m₁ m₂ n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (R : Fin m₁ → Fin (2 + n) → K) (S : Fin m₂ → Fin (2 + n) → K) : Prop :=
  ∃ e : (Fin (2 + n) → K) ≃ₗ[K] (Fin (2 + n) → K),
    IsSplitIsometryWitness (K := K) c e ∧
    SameCode (linearEquivFamily e R) S

theorem splitIsometryCodeEquiv_to_headAlignmentCodeEquiv
    {m₁ m₂ n : ℕ} [Fact ((2 : K) ≠ 0)] {c : K}
    {R : Fin m₁ → Fin (2 + n) → K} {S : Fin m₂ → Fin (2 + n) → K}
    (h : SplitIsometryCodeEquiv (K := K) c R S) :
    HeadAlignmentCodeEquiv (K := K) c R S := by
  rcases h with ⟨e, he, hcode⟩
  exact ⟨e, he.head, hcode⟩

theorem splitIsometryCodeEquiv_to_ambientLinearCodeEquiv
    {m₁ m₂ n : ℕ} [Fact ((2 : K) ≠ 0)] {c : K}
    {R : Fin m₁ → Fin (2 + n) → K} {S : Fin m₂ → Fin (2 + n) → K}
    (h : SplitIsometryCodeEquiv (K := K) c R S) :
    AmbientLinearCodeEquiv (K := K) R S := by
  rcases h with ⟨e, _he, hcode⟩
  exact ⟨e, hcode⟩

def ReverseSplitEquiv {m n : ℕ} [Fact ((2 : K) ≠ 0)]
    (c : K) (R S : Fin (m + 1) → Fin (2 + n) → K) : Prop :=
  ∃ T : Fin (m + 1) → Fin (2 + n) → K,
    SameCode T R ∧ HeadAlignCodeEquiv (K := K) c T S

theorem reverseSplitEquiv_intro
    {m n : ℕ} [Fact ((2 : K) ≠ 0)] {c : K}
    {R S T : Fin (m + 1) → Fin (2 + n) → K}
    (hcode : SameCode T R)
    (halign : HeadAlignCodeEquiv (K := K) c T S) :
    ReverseSplitEquiv (K := K) c R S := by
  exact ⟨T, hcode, halign⟩

theorem headAlignLinearEquiv_isHeadAlignmentWitness
    {n : ℕ} [Fact ((2 : K) ≠ 0)] {c : K}
    (hc : c ^ 2 = (-1 : K)) :
    IsHeadAlignmentWitness (K := K) c
      (headAlignLinearEquiv (K := K) (n := n) c hc) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact splitTail_headAlignFamilyVec (K := K) c v
  · intro x
    exact headAlignFamilyVec_pivot (K := K) (n := n) c hc x
  · intro g
    exact headAlignFamilyVec_zeroHead (K := K) (n := n) c g

theorem headAlignLinearEquiv_isSplitIsometryWitness
    {n : ℕ} [Fact ((2 : K) ≠ 0)] {c : K}
    (hc : c ^ 2 = (-1 : K)) :
    IsSplitIsometryWitness (K := K) c
      (headAlignLinearEquiv (K := K) (n := n) c hc) := by
  refine ⟨headAlignLinearEquiv_isHeadAlignmentWitness (K := K) (n := n) hc, ?_⟩
  intro u v
  exact splitDot_headAlignFamilyVec (K := K) hc u v

theorem headAlignCodeEquiv_to_headAlignmentCodeEquiv
    {m₁ m₂ n : ℕ} [Fact ((2 : K) ≠ 0)] {c : K}
    (hc : c ^ 2 = (-1 : K))
    {R : Fin m₁ → Fin (2 + n) → K} {S : Fin m₂ → Fin (2 + n) → K}
    (h : HeadAlignCodeEquiv (K := K) c R S) :
    HeadAlignmentCodeEquiv (K := K) c R S := by
  refine ⟨headAlignLinearEquiv (K := K) (n := n) c hc,
    headAlignLinearEquiv_isHeadAlignmentWitness (K := K) (n := n) hc, ?_⟩
  simpa [HeadAlignmentCodeEquiv, HeadAlignCodeEquiv, linearEquivFamily,
    headAlignLinearEquiv, headAlignFamily] using h

theorem headAlignCodeEquiv_to_splitIsometryCodeEquiv
    {m₁ m₂ n : ℕ} [Fact ((2 : K) ≠ 0)] {c : K}
    (hc : c ^ 2 = (-1 : K))
    {R : Fin m₁ → Fin (2 + n) → K} {S : Fin m₂ → Fin (2 + n) → K}
    (h : HeadAlignCodeEquiv (K := K) c R S) :
    SplitIsometryCodeEquiv (K := K) c R S := by
  refine ⟨headAlignLinearEquiv (K := K) (n := n) c hc,
    headAlignLinearEquiv_isSplitIsometryWitness (K := K) (n := n) hc, ?_⟩
  simpa [SplitIsometryCodeEquiv, HeadAlignCodeEquiv, linearEquivFamily,
    headAlignLinearEquiv, headAlignFamily] using h

theorem headAlignCodeEquiv_to_ambientLinearCodeEquiv
    {m₁ m₂ n : ℕ} [Fact ((2 : K) ≠ 0)] {c : K}
    (hc : c ^ 2 = (-1 : K))
    {R : Fin m₁ → Fin (2 + n) → K} {S : Fin m₂ → Fin (2 + n) → K}
    (h : HeadAlignCodeEquiv (K := K) c R S) :
    AmbientLinearCodeEquiv (K := K) R S := by
  refine ⟨headAlignLinearEquiv (K := K) (n := n) c hc, ?_⟩
  simpa [AmbientLinearCodeEquiv, HeadAlignCodeEquiv, linearEquivFamily,
    headAlignLinearEquiv, headAlignFamily]
    using h

theorem reverseSplitEquiv_to_ambientLinearCodeEquiv
    {m n : ℕ} [Fact ((2 : K) ≠ 0)] {c : K}
    (hc : c ^ 2 = (-1 : K))
    {R S : Fin (m + 1) → Fin (2 + n) → K}
    (h : ReverseSplitEquiv (K := K) c R S) :
    AmbientLinearCodeEquiv (K := K) R S := by
  rcases h with ⟨T, hcode, halign⟩
  rcases headAlignCodeEquiv_to_ambientLinearCodeEquiv (K := K) (m₁ := m + 1)
      (m₂ := m + 1) (n := n) hc halign with ⟨e, hTS⟩
  refine ⟨e, ?_⟩
  exact sameCode_trans
    (sameCode_linearEquivFamily (K := K) e (sameCode_symm hcode))
    hTS

theorem reverseSplitEquiv_to_headAlignmentCodeEquiv
    {m n : ℕ} [Fact ((2 : K) ≠ 0)] {c : K}
    (hc : c ^ 2 = (-1 : K))
    {R S : Fin (m + 1) → Fin (2 + n) → K}
    (h : ReverseSplitEquiv (K := K) c R S) :
    HeadAlignmentCodeEquiv (K := K) c R S := by
  rcases h with ⟨T, hcode, halign⟩
  rcases headAlignCodeEquiv_to_headAlignmentCodeEquiv (K := K)
      (m₁ := m + 1) (m₂ := m + 1) (n := n) hc halign with ⟨e, he, hTS⟩
  refine ⟨e, he, ?_⟩
  exact sameCode_trans
    (sameCode_linearEquivFamily (K := K) e (sameCode_symm hcode))
    hTS

theorem reverseSplitEquiv_to_splitIsometryCodeEquiv
    {m n : ℕ} [Fact ((2 : K) ≠ 0)] {c : K}
    (hc : c ^ 2 = (-1 : K))
    {R S : Fin (m + 1) → Fin (2 + n) → K}
    (h : ReverseSplitEquiv (K := K) c R S) :
    SplitIsometryCodeEquiv (K := K) c R S := by
  rcases h with ⟨T, hcode, halign⟩
  rcases headAlignCodeEquiv_to_splitIsometryCodeEquiv (K := K)
      (m₁ := m + 1) (m₂ := m + 1) (n := n) hc halign with ⟨e, he, hTS⟩
  refine ⟨e, he, ?_⟩
  exact sameCode_trans
    (sameCode_linearEquivFamily (K := K) e (sameCode_symm hcode))
    hTS

theorem exists_headAligned_buildRows_of_pairwiseOrthogonal_isotropicHeadFamily
    {m n : ℕ} [Fact ((2 : K) ≠ 0)]
    (i₀ : Fin (m + 1)) {a c : K}
    (R : Fin (m + 1) → Fin (2 + n) → K)
    (g : Fin n → K) (ha : a ≠ 0)
    (hc : c ^ 2 = (-1 : K))
    (hrow : R i₀ = prepend2 a (c * a) g)
    (hall : ∀ j : Fin (m + 1), HasIsotropicHead (K := K) c (R j))
    (horth : PairwiseOrthogonal (K := K) R) :
    ∃ x : Fin n → K, ∃ a' : Fin m → K, ∃ G : Fin m → Fin n → K,
      SameCode (pivotPureTailRows x c a' G) R ∧
      HeadAlignCodeEquiv (K := K) c
        (pivotPureTailRows x c a' G)
        (buildRows x c (pivotResidualTails x a' G)) ∧
      IsOrthogonalTailFamily (K := K) x (pivotResidualTails x a' G) := by
  rcases exists_pivotPureTailRows_sameCode_and_isOrthogonalTailFamily
      (K := K) i₀ R g ha hc hrow hall horth with
    ⟨x, a', G, hcode, _hpureOrth, htail⟩
  have htail' : IsOrthogonalTailFamily (K := K) x (pivotResidualTails x a' G) := by
    simpa [deleteHyperbolicPairSplit_pivotPureTailRows (K := K) x c a' G] using htail
  refine ⟨x, a', G, hcode, ?_, htail'⟩
  unfold HeadAlignCodeEquiv
  rw [headAlignFamily_pivotPureTailRows_eq_buildRows (K := K) (a := a') (G := G) hc htail']

theorem exists_reverseSplitEquiv_buildRows_of_pairwiseOrthogonal_isotropicHeadFamily
    {m n : ℕ} [Fact ((2 : K) ≠ 0)]
    (i₀ : Fin (m + 1)) {a c : K}
    (R : Fin (m + 1) → Fin (2 + n) → K)
    (g : Fin n → K) (ha : a ≠ 0)
    (hc : c ^ 2 = (-1 : K))
    (hrow : R i₀ = prepend2 a (c * a) g)
    (hall : ∀ j : Fin (m + 1), HasIsotropicHead (K := K) c (R j))
    (horth : PairwiseOrthogonal (K := K) R) :
    ∃ x : Fin n → K, ∃ a' : Fin m → K, ∃ G : Fin m → Fin n → K,
      ReverseSplitEquiv (K := K) c R
        (buildRows x c (pivotResidualTails x a' G)) ∧
      IsOrthogonalTailFamily (K := K) x (pivotResidualTails x a' G) := by
  rcases exists_headAligned_buildRows_of_pairwiseOrthogonal_isotropicHeadFamily
      (K := K) i₀ R g ha hc hrow hall horth with
    ⟨x, a', G, hcode, halign, htail⟩
  refine ⟨x, a', G, ?_, htail⟩
  exact reverseSplitEquiv_intro (K := K) hcode halign

theorem exists_ambientLinearCodeEquiv_buildRows_of_pairwiseOrthogonal_isotropicHeadFamily
    {m n : ℕ} [Fact ((2 : K) ≠ 0)]
    (i₀ : Fin (m + 1)) {a c : K}
    (R : Fin (m + 1) → Fin (2 + n) → K)
    (g : Fin n → K) (ha : a ≠ 0)
    (hc : c ^ 2 = (-1 : K))
    (hrow : R i₀ = prepend2 a (c * a) g)
    (hall : ∀ j : Fin (m + 1), HasIsotropicHead (K := K) c (R j))
    (horth : PairwiseOrthogonal (K := K) R) :
    ∃ x : Fin n → K, ∃ a' : Fin m → K, ∃ G : Fin m → Fin n → K,
      AmbientLinearCodeEquiv (K := K) R
        (buildRows x c (pivotResidualTails x a' G)) ∧
      IsOrthogonalTailFamily (K := K) x (pivotResidualTails x a' G) := by
  rcases exists_reverseSplitEquiv_buildRows_of_pairwiseOrthogonal_isotropicHeadFamily
      (K := K) i₀ R g ha hc hrow hall horth with
    ⟨x, a', G, hrev, htail⟩
  refine ⟨x, a', G, ?_, htail⟩
  exact reverseSplitEquiv_to_ambientLinearCodeEquiv (K := K) hc hrev

theorem exists_headAlignmentCodeEquiv_buildRows_of_pairwiseOrthogonal_isotropicHeadFamily
    {m n : ℕ} [Fact ((2 : K) ≠ 0)]
    (i₀ : Fin (m + 1)) {a c : K}
    (R : Fin (m + 1) → Fin (2 + n) → K)
    (g : Fin n → K) (ha : a ≠ 0)
    (hc : c ^ 2 = (-1 : K))
    (hrow : R i₀ = prepend2 a (c * a) g)
    (hall : ∀ j : Fin (m + 1), HasIsotropicHead (K := K) c (R j))
    (horth : PairwiseOrthogonal (K := K) R) :
    ∃ x : Fin n → K, ∃ a' : Fin m → K, ∃ G : Fin m → Fin n → K,
      HeadAlignmentCodeEquiv (K := K) c R
        (buildRows x c (pivotResidualTails x a' G)) ∧
      IsOrthogonalTailFamily (K := K) x (pivotResidualTails x a' G) := by
  rcases exists_reverseSplitEquiv_buildRows_of_pairwiseOrthogonal_isotropicHeadFamily
      (K := K) i₀ R g ha hc hrow hall horth with
    ⟨x, a', G, hrev, htail⟩
  refine ⟨x, a', G, ?_, htail⟩
  exact reverseSplitEquiv_to_headAlignmentCodeEquiv (K := K) hc hrev

theorem exists_splitIsometryCodeEquiv_buildRows_of_pairwiseOrthogonal_isotropicHeadFamily
    {m n : ℕ} [Fact ((2 : K) ≠ 0)]
    (i₀ : Fin (m + 1)) {a c : K}
    (R : Fin (m + 1) → Fin (2 + n) → K)
    (g : Fin n → K) (ha : a ≠ 0)
    (hc : c ^ 2 = (-1 : K))
    (hrow : R i₀ = prepend2 a (c * a) g)
    (hall : ∀ j : Fin (m + 1), HasIsotropicHead (K := K) c (R j))
    (horth : PairwiseOrthogonal (K := K) R) :
    ∃ x : Fin n → K, ∃ a' : Fin m → K, ∃ G : Fin m → Fin n → K,
      SplitIsometryCodeEquiv (K := K) c R
        (buildRows x c (pivotResidualTails x a' G)) ∧
      IsOrthogonalTailFamily (K := K) x (pivotResidualTails x a' G) := by
  rcases exists_reverseSplitEquiv_buildRows_of_pairwiseOrthogonal_isotropicHeadFamily
      (K := K) i₀ R g ha hc hrow hall horth with
    ⟨x, a', G, hrev, htail⟩
  refine ⟨x, a', G, ?_, htail⟩
  exact reverseSplitEquiv_to_splitIsometryCodeEquiv (K := K) hc hrev

theorem exists_buildRows_up_to_splitIsometry_of_pairwiseOrthogonal_isotropicHeadFamily
    {m n : ℕ} [Fact ((2 : K) ≠ 0)]
    (i₀ : Fin (m + 1)) {a c : K}
    (R : Fin (m + 1) → Fin (2 + n) → K)
    (g : Fin n → K) (ha : a ≠ 0)
    (hc : c ^ 2 = (-1 : K))
    (hrow : R i₀ = prepend2 a (c * a) g)
    (hall : ∀ j : Fin (m + 1), HasIsotropicHead (K := K) c (R j))
    (horth : PairwiseOrthogonal (K := K) R) :
    ∃ x : Fin n → K, ∃ a' : Fin m → K, ∃ G : Fin m → Fin n → K,
      SplitIsometryCodeEquiv (K := K) c R
        (buildRows x c (pivotResidualTails x a' G)) ∧
      IsOrthogonalTailFamily (K := K) x (pivotResidualTails x a' G) := by
  exact exists_splitIsometryCodeEquiv_buildRows_of_pairwiseOrthogonal_isotropicHeadFamily
    (K := K) i₀ R g ha hc hrow hall horth

theorem codeEquiv_of_sameCode
    {m₁ m₂ n : ℕ}
    {R : Fin m₁ → Fin n → K} {S : Fin m₂ → Fin n → K}
    (h : SameCode R S) : CodeEquiv R S := by
  refine ⟨Equiv.refl (Fin n), ?_⟩
  simpa [CodeEquiv, SameCode, permuteFamily, permuteVec] using h

theorem codeEquiv_refl {m n : ℕ} (R : Fin m → Fin n → K) : CodeEquiv R R := by
  exact codeEquiv_of_sameCode (sameCode_refl R)

theorem sameCode_deleteHyperbolicPairSplit_buildRows
    {m n : ℕ} (x : Fin n → K) (c : K) (G : Fin m → Fin n → K) :
    SameCode (deleteHyperbolicPairSplit (K := K) (buildRows x c G)) G := by
  apply sameCode_of_eq
  exact deleteHyperbolicPairSplit_buildRows (K := K) x c G

theorem codeEquiv_deleteHyperbolicPairSplit_buildRows
    {m n : ℕ} (x : Fin n → K) (c : K) (G : Fin m → Fin n → K) :
    CodeEquiv (deleteHyperbolicPairSplit (K := K) (buildRows x c G)) G := by
  exact codeEquiv_of_sameCode
    (sameCode_deleteHyperbolicPairSplit_buildRows (K := K) x c G)

theorem sameCode_rebuild_of_IsSplitBuildFamily
    {m n : ℕ} {x : Fin n → K} {c : K}
    {R : Fin (m + 1) → Fin (2 + n) → K}
    (hR : IsSplitBuildFamily (K := K) x c R) :
    SameCode (buildRows x c (deleteHyperbolicPairSplit (K := K) R)) R := by
  apply sameCode_of_eq
  exact buildRows_deleteHyperbolicPairSplit_eq (K := K) hR

theorem codeEquiv_rebuild_of_IsSplitBuildFamily
    {m n : ℕ} {x : Fin n → K} {c : K}
    {R : Fin (m + 1) → Fin (2 + n) → K}
    (hR : IsSplitBuildFamily (K := K) x c R) :
    CodeEquiv (buildRows x c (deleteHyperbolicPairSplit (K := K) R)) R := by
  exact codeEquiv_of_sameCode
    (sameCode_rebuild_of_IsSplitBuildFamily (K := K) hR)

theorem sameCode_delete_buildRowsBin
    {m n : ℕ} (x : Fin n → K) (G : Fin m → Fin n → K) :
    SameCode (deleteHyperbolicPair (buildRowsBin x G)) G := by
  apply sameCode_of_eq
  exact deleteHyperbolicPair_buildRowsBin x G

theorem codeEquiv_delete_buildRowsBin
    {m n : ℕ} (x : Fin n → K) (G : Fin m → Fin n → K) :
    CodeEquiv (deleteHyperbolicPair (buildRowsBin x G)) G := by
  exact codeEquiv_of_sameCode (sameCode_delete_buildRowsBin x G)

theorem sameCode_rebuild_of_IsBoxedKimFamily
    {m n : ℕ} {x : Fin n → K} {R : Fin (m + 1) → Fin (2 + n) → K}
    (hR : IsBoxedKimFamily x R) :
    SameCode (buildRowsBin x (deleteHyperbolicPair R)) R := by
  apply sameCode_of_eq
  exact rebuild_of_IsBoxedKimFamily hR

theorem codeEquiv_rebuild_of_IsBoxedKimFamily
    {m n : ℕ} {x : Fin n → K} {R : Fin (m + 1) → Fin (2 + n) → K}
    (hR : IsBoxedKimFamily x R) :
    CodeEquiv (buildRowsBin x (deleteHyperbolicPair R)) R := by
  exact codeEquiv_of_sameCode (sameCode_rebuild_of_IsBoxedKimFamily hR)

theorem sameCode_boxedFamily_buildRowsBin
    {m n : ℕ}
    {x : Fin n → K} {Y : Fin m → K} {G : Fin m → Fin n → K}
    (hY : ∀ i : Fin m, Y i = dot x (G i)) :
    SameCode (boxedFamily x Y G) (buildRowsBin x G) := by
  apply sameCode_of_eq
  exact boxedFamily_eq_buildRowsBin hY

theorem codeEquiv_boxedFamily_buildRowsBin
    {m n : ℕ}
    {x : Fin n → K} {Y : Fin m → K} {G : Fin m → Fin n → K}
    (hY : ∀ i : Fin m, Y i = dot x (G i)) :
    CodeEquiv (boxedFamily x Y G) (buildRowsBin x G) := by
  exact codeEquiv_of_sameCode (sameCode_boxedFamily_buildRowsBin hY)

end BinaryBoxedReduction

section CharTwoPart

variable {K : Type*} [Field K] [CharP K 2]

theorem two_eq_zero : (2 : K) = 0 := by
  exact CharP.cast_eq_zero (R := K) 2

theorem dot_r0_r0_bin
    {n : ℕ} {x : Fin n → K}
    (hx : dot x x = (1 : K)) :
    dot (r0 x) (r0 x) = 0 := by
  rw [r0, dot_prepend2_prepend2, hx]
  calc
    (1 : K) * 1 + 0 * 0 + 1 = (2 : K) := by ring
    _ = 0 := two_eq_zero

theorem dot_r0_riBin
    {n : ℕ} {x g : Fin n → K} {yi : K}
    (hyi : yi = dot x g) :
    dot (r0 x) (riBin yi g) = 0 := by
  rw [r0, riBin, dot_prepend2_prepend2, hyi]
  calc
    (1 : K) * dot x g + 0 * dot x g + dot x g = (2 : K) * dot x g := by ring
    _ = 0 := by rw [two_eq_zero, zero_mul]

theorem dot_riBin_riBin
    {n : ℕ} {g h : Fin n → K} {yi yj : K}
    (hgh : dot g h = 0) :
    dot (riBin yi g) (riBin yj h) = 0 := by
  rw [riBin, riBin, dot_prepend2_prepend2, hgh]
  calc
    yi * yj + yi * yj + 0 = (2 : K) * (yi * yj) := by ring
    _ = 0 := by rw [two_eq_zero, zero_mul]

theorem buildRowsBin_zero_zero
    {m n : ℕ} {x : Fin n → K} {G : Fin m → Fin n → K}
    (hx : dot x x = (1 : K)) :
    dot (buildRowsBin x G 0) (buildRowsBin x G 0) = 0 := by
  simp [buildRowsBin]
  exact dot_r0_r0_bin hx

theorem buildRowsBin_zero_succ
    {m n : ℕ} {x : Fin n → K} {G : Fin m → Fin n → K}
    (i : Fin m) :
    dot (buildRowsBin x G 0) (buildRowsBin x G (Fin.succ i)) = 0 := by
  simp [buildRowsBin]
  exact dot_r0_riBin rfl

theorem buildRowsBin_succ_zero
    {m n : ℕ} {x : Fin n → K} {G : Fin m → Fin n → K}
    (i : Fin m) :
    dot (buildRowsBin x G (Fin.succ i)) (buildRowsBin x G 0) = 0 := by
  rw [dot_comm]
  exact buildRowsBin_zero_succ i

theorem buildRowsBin_succ_succ
    {m n : ℕ} {x : Fin n → K} {G : Fin m → Fin n → K}
    (hG : ∀ i j : Fin m, dot (G i) (G j) = 0)
    (i j : Fin m) :
    dot (buildRowsBin x G (Fin.succ i)) (buildRowsBin x G (Fin.succ j)) = 0 := by
  simp [buildRowsBin]
  exact dot_riBin_riBin (hgh := hG i j)

theorem buildRowsBin_orthogonal
    {m n : ℕ} {x : Fin n → K} {G : Fin m → Fin n → K}
    (hx : dot x x = (1 : K))
    (hG : ∀ i j : Fin m, dot (G i) (G j) = 0) :
    ∀ i j : Fin (m + 1), dot (buildRowsBin x G i) (buildRowsBin x G j) = 0 := by
  intro i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact buildRowsBin_zero_zero hx
    · exact buildRowsBin_zero_succ j
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact buildRowsBin_succ_zero i
    · exact buildRowsBin_succ_succ (hG := hG) i j

theorem buildRowsBin_matrix_gram_zero
    {m n : ℕ} {x : Fin n → K} {G : Fin m → Fin n → K}
    (hx : dot x x = (1 : K))
    (hG : ∀ i j : Fin m, dot (G i) (G j) = 0) :
    rowMatrix (buildRowsBin x G) * (rowMatrix (buildRowsBin x G)).transpose = 0 := by
  ext i j
  rw [rowMatrix_mul_transpose_apply]
  exact buildRowsBin_orthogonal (hx := hx) (hG := hG) i j

theorem boxedFamily_matrix_gram_zero
    {m n : ℕ}
    {x : Fin n → K} {Y : Fin m → K} {G : Fin m → Fin n → K}
    (hx : dot x x = (1 : K))
    (hY : ∀ i : Fin m, Y i = dot x (G i))
    (hG : ∀ i j : Fin m, dot (G i) (G j) = 0) :
    rowMatrix (boxedFamily x Y G) * (rowMatrix (boxedFamily x Y G)).transpose = 0 := by
  rw [boxedFamily_eq_buildRowsBin hY]
  exact buildRowsBin_matrix_gram_zero (hx := hx) (hG := hG)

end CharTwoPart

section CurrentPaperTheoremSpine

/-!
The declarations in this section expose paper-facing theorem wrappers for the
current version of `paper.tex`. They are intentionally compact: the goal is to
connect the paper statements to already-proved linear-algebraic cores in this
single Lean file, rather than to duplicate the full prose-level statements.
-/

section Binary

variable {K : Type*} [Field K] [CharP K 2]

/-- Lean core for the binary Kim building-up step. -/
theorem paper_binary_kim_building_up_core
    {m n : ℕ} {x : Fin n → K} {G : Fin m → Fin n → K}
    (hx : dot x x = (1 : K))
    (hG : ∀ i j : Fin m, dot (G i) (G j) = 0) :
    rowMatrix (buildRowsBin x G) * (rowMatrix (buildRowsBin x G)).transpose = 0 := by
  exact buildRowsBin_matrix_gram_zero (K := K) hx hG

/-- Lean core for the theorem-level CZ--Kim equivalence in the binary section. -/
theorem paper_binary_cz_kim_equivalence
    {m n : ℕ} {x : Fin n → K} {R : Fin (m + 1) → Fin (2 + n) → K}
    (hR : IsBoxedKimFamily x R) :
    CodeEquiv (buildRowsBin x (deleteHyperbolicPair R)) R := by
  exact codeEquiv_rebuild_of_IsBoxedKimFamily (K := K) hR

/-- The boxed binary family agrees with the Kim family once the coefficients are
identified with the dot products against the extension vector. -/
theorem paper_binary_boxed_equals_kim
    {m n : ℕ} {x : Fin n → K} {Y : Fin m → K} {G : Fin m → Fin n → K}
    (hY : ∀ i : Fin m, Y i = dot x (G i)) :
    SameCode (boxedFamily x Y G) (buildRowsBin x G) := by
  exact sameCode_boxedFamily_buildRowsBin (K := K) hY

end Binary

section SplitQary

variable {K : Type*} [Field K]

/-- Paper-facing rebuild statement for the adapted split theorem. -/
theorem paper_qary_building_up_rebuild
    {m n : ℕ} {x : Fin n → K} {c : K}
    {R : Fin (m + 1) → Fin (2 + n) → K}
    (hR : IsSplitBuildFamily (K := K) x c R) :
    buildRows x c (deleteHyperbolicPairSplit (K := K) R) = R := by
  exact buildRows_deleteHyperbolicPairSplit_eq (K := K) hR

/-- Forward self-duality statement used for the split building-up theorem. -/
theorem paper_qary_building_up_forward_self_dual
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hx : dot x x = (-1 : K))
    (hc : c ^ 2 = (-1 : K))
    (hGorth : ∀ i j : Fin m, dot (G i) (G j) = 0)
    (hGlin : LinearIndependent K G)
    (heven : Even n)
    (hcard : m + 1 = (n + 2) / 2) :
    rowSpace (buildRows x c G) =
      (dotBilin (K := K) (n := 2 + n)).orthogonal
        (rowSpace (buildRows x c G)) := by
  exact buildRows_rowSpace_self_dual_of_self_dual_parent_basis
    (K := K) (hx := hx) (hc := hc) (hGorth := hGorth)
    (hGlin := hGlin) (heven := heven) (hcard := hcard)

/-- Lean core underlying the forward split boxed theorem in the paper.

The paper states this theorem in boxed matrix coordinates; in Lean the same
forward self-duality mechanism is formalized through `buildRows`.
-/
theorem paper_split_boxed_form_forward_core
    {m n : ℕ} {x : Fin n → K} {c : K} {G : Fin m → Fin n → K}
    (hx : dot x x = (-1 : K))
    (hc : c ^ 2 = (-1 : K))
    (hGorth : ∀ i j : Fin m, dot (G i) (G j) = 0)
    (hGlin : LinearIndependent K G)
    (heven : Even n)
    (hcard : m + 1 = (n + 2) / 2) :
    rowSpace (buildRows x c G) =
      (dotBilin (K := K) (n := 2 + n)).orthogonal
        (rowSpace (buildRows x c G)) := by
  exact paper_qary_building_up_forward_self_dual
    (K := K) (hx := hx) (hc := hc) (hGorth := hGorth)
    (hGlin := hGlin) (heven := heven) (hcard := hcard)

/-- Lean core for the conditional boxed normalization theorem.

The current paper states this in boxed coefficient language. In Lean the same
reverse mechanism is captured by the existence of a split-isometric equivalence
to a `buildRows` family once the rows have a suitable isotropic head and are
pairwise orthogonal.
-/
theorem paper_conditional_split_boxed_normalization_core
    {m n : ℕ} [Fact ((2 : K) ≠ 0)]
    (i₀ : Fin (m + 1)) {a c : K}
    (R : Fin (m + 1) → Fin (2 + n) → K)
    (g : Fin n → K) (ha : a ≠ 0)
    (hc : c ^ 2 = (-1 : K))
    (hrow : R i₀ = prepend2 a (c * a) g)
    (hall : ∀ j : Fin (m + 1), HasIsotropicHead (K := K) c (R j))
    (horth : PairwiseOrthogonal (K := K) R) :
    ∃ x : Fin n → K, ∃ a' : Fin m → K, ∃ G : Fin m → Fin n → K,
      SplitIsometryCodeEquiv (K := K) c R
        (buildRows x c (pivotResidualTails x a' G)) ∧
      IsOrthogonalTailFamily (K := K) x (pivotResidualTails x a' G) := by
  exact exists_splitIsometryCodeEquiv_buildRows_of_pairwiseOrthogonal_isotropicHeadFamily
    (K := K) i₀ R g ha hc hrow hall horth

end SplitQary

end CurrentPaperTheoremSpine

/-!
## Coverage table for the current paper version

This is a compact status table for the paper body theorem spine.

- `def:sd`, `def:lagrangian`, `prop:systematic-form`
  - status: covered through the common bilinear-space core in this file
- `thm-binary-build-1`
  - Lean: `paper_binary_kim_building_up_core`
  - status: reused
- `thm:CZ_Kim_Lagrangian` / `thm:binary-cz-kim`
  - Lean: `paper_binary_cz_kim_equivalence`
  - status: reused as theorem-level linear-algebraic core
- `thm:qary-building-up`
  - Lean: `paper_qary_building_up_rebuild`,
    `paper_qary_building_up_forward_self_dual`
  - status: reused and packaged
- `thm:split-boxed-form`
  - Lean: `paper_split_boxed_form_forward_core`
  - status: formalized through the `buildRows` forward self-duality core
- `thm:conditional-split-boxed-normalization`
  - Lean: `paper_conditional_split_boxed_normalization_core`
  - status: formalized through the existing reverse-up-to-split-isometry core

The explicit GF(5)/GF(13) application examples in the paper are intentionally
not formalized in this Lean completion pass.
-/
