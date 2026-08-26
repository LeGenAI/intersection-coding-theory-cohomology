import Formalization.Archive.SubmittedBaseline

set_option autoImplicit false

namespace BuildingUpFormalization.Components.NormForm

variable {K : Type*} [Field K]

/-- A square root of `-1` has multiplicative order four in odd
characteristic. -/
theorem root_neg_one_orderOf
    [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    orderOf c = 4 := by
  have hneg_one_ne_one : (-1 : K) ≠ 1 := by
    intro h
    have htwo : (2 : K) = 0 := by
      calc
        (2 : K) = 1 - (-1 : K) := by ring
        _ = 1 - 1 := by rw [h]
        _ = 0 := by ring
    exact (Fact.out : (2 : K) ≠ 0) htwo
  apply (orderOf_eq_iff (x := c) (by norm_num : 0 < 4)).2
  constructor
  · calc
      c ^ 4 = (c ^ 2) ^ 2 := by ring
      _ = (-1 : K) ^ 2 := by rw [hc]
      _ = 1 := by ring
  · intro m hm4 hm0
    have hm : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hm with rfl | rfl | rfl
    · intro hc1
      have hc_eq_one : c = 1 := by simpa using hc1
      apply hneg_one_ne_one
      calc
        (-1 : K) = c ^ 2 := hc.symm
        _ = 1 := by rw [hc_eq_one]; norm_num
    · intro hc2
      exact hneg_one_ne_one (hc.symm.trans hc2)
    · intro hc3
      have hc_eq_neg_one : c = (-1 : K) := by
        have hminus : -c = (1 : K) := by
          calc
            -c = c ^ 3 := by
              calc
                -c = (-1 : K) * c := by ring
                _ = c ^ 2 * c := by rw [hc]
                _ = c ^ 3 := by ring
            _ = 1 := hc3
        linear_combination -hminus
      apply hneg_one_ne_one
      calc
        (-1 : K) = c ^ 2 := hc.symm
        _ = (-1 : K) ^ 2 := by rw [hc_eq_neg_one]
        _ = 1 := by ring

/-- The explicit scalar-matrix solution in Proposition 2.2(iii). -/
theorem scalar_identity_mul_transpose
    {k : ℕ} (c : K) (hc : c ^ 2 = (-1 : K)) :
    (c • (1 : Matrix (Fin k) (Fin k) K)) *
        (c • (1 : Matrix (Fin k) (Fin k) K)).transpose =
      -(1 : Matrix (Fin k) (Fin k) K) := by
  rw [Matrix.transpose_smul, Matrix.transpose_one]
  calc
    (c • (1 : Matrix (Fin k) (Fin k) K)) *
        (c • (1 : Matrix (Fin k) (Fin k) K)) =
      c • ((1 : Matrix (Fin k) (Fin k) K) *
        (c • (1 : Matrix (Fin k) (Fin k) K))) := by
          rw [smul_mul_assoc]
    _ = c • (c • ((1 : Matrix (Fin k) (Fin k) K) * 1)) := by
      rw [mul_smul_comm]
    _ = (c * c) • (1 : Matrix (Fin k) (Fin k) K) := by
      simp [smul_smul]
    _ = -(1 : Matrix (Fin k) (Fin k) K) := by
      rw [← pow_two c, hc]
      simp

/-- The two vectors displayed in Proposition 2.3 are exactly a hyperbolic
pair for the Euclidean dot product. -/
theorem splitE1_splitE2_hyperbolicPair
    [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    paperHyperbolicPair (K := K) (splitE1 c) (splitE2 c) := by
  have h2 : (2 : K) ≠ 0 := Fact.out
  constructor
  · simp only [splitE1, dot, Fin.sum_univ_two, head2]
    rw [← pow_two c, hc]
    ring
  · constructor
    · simp only [splitE2, dot, Fin.sum_univ_two, head2]
      field_simp [h2]
      rw [hc]
      ring
    · simp only [splitE1, splitE2, dot, Fin.sum_univ_two, head2]
      field_simp [h2]
      rw [hc]
      ring

theorem splitE1_splitE2_linearIndependent
    [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    LinearIndependent K ![splitE1 c, splitE2 c] := by
  have hpair := splitE1_splitE2_hyperbolicPair c hc
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hs : s = 0 := by
    have h := congrArg (fun v => dot v (splitE2 c)) hst
    change dot (s • splitE1 c + t • splitE2 c) (splitE2 c) =
      dot 0 (splitE2 c) at h
    rw [dot_add_left, dot_smul_left, dot_smul_left] at h
    have hz : dot (0 : Fin 2 → K) (splitE2 c) = 0 := by simp [dot]
    simpa [hpair.2.1, hpair.2.2, hz] using h
  have ht : t = 0 := by
    have h := congrArg (fun v => dot v (splitE1 c)) hst
    change dot (s • splitE1 c + t • splitE2 c) (splitE1 c) =
      dot 0 (splitE1 c) at h
    rw [dot_add_left, dot_smul_left, dot_smul_left] at h
    have hcross : dot (splitE2 c) (splitE1 c) = 1 := by
      rw [dot_comm]
      exact hpair.2.2
    have hz : dot (0 : Fin 2 → K) (splitE1 c) = 0 := by simp [dot]
    simpa [hpair.1, hcross, hz] using h
  exact ⟨hs, ht⟩

/-- The factor order used in the manuscript. -/
theorem norm_form_splitting_paper_order
    (c x y : K) (hc : c ^ 2 = (-1 : K)) :
    x ^ 2 + y ^ 2 = (x - c * y) * (x + c * y) := by
  rw [norm_form_splitting c x y hc]
  ring

/-- The explicit witness with its two factors evaluated. This removes the sign
ambiguity between equivalent formulas for `y`. -/
theorem norm_form_witness_factors
    [Fact ((2 : K) ≠ 0)] (a c : K) (hc : c ^ 2 = (-1 : K)) :
    let x : K := (1 + a) / 2
    let y : K := ((1 - a) / 2) * c
    x - c * y = 1 ∧ x + c * y = a ∧ x ^ 2 + y ^ 2 = a := by
  dsimp
  have h2 : (2 : K) ≠ 0 := Fact.out
  constructor
  · field_simp [h2]
    rw [hc]
    ring
  · constructor
    · field_simp [h2]
      rw [hc]
      ring
    · exact norm_form_witness (K := K) a c hc

theorem exists_norm_pair_with_paper_factors
    [Fact ((2 : K) ≠ 0)] (a c : K) (hc : c ^ 2 = (-1 : K)) :
    ∃ x y : K,
      x - c * y = 1 ∧ x + c * y = a ∧ x ^ 2 + y ^ 2 = a := by
  refine ⟨(1 + a) / 2, ((1 - a) / 2) * c, ?_⟩
  exact norm_form_witness_factors a c hc

/-- Exact paper-facing package for all four conclusions of Proposition 2.2. -/
theorem paper_split_consequences_exact
    [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    orderOf c = 4 ∧
      (paperHyperbolicPair (K := K) (splitE1 c) (splitE2 c) ∧
        LinearIndependent K ![splitE1 c, splitE2 c]) ∧
      (∀ k : ℕ,
        (c • (1 : Matrix (Fin k) (Fin k) K)) *
            (c • (1 : Matrix (Fin k) (Fin k) K)).transpose =
          -(1 : Matrix (Fin k) (Fin k) K)) ∧
      (∀ a : K, ∃ x y : K,
        x - c * y = 1 ∧ x + c * y = a ∧ x ^ 2 + y ^ 2 = a) := by
  exact ⟨root_neg_one_orderOf c hc,
    ⟨splitE1_splitE2_hyperbolicPair c hc,
      splitE1_splitE2_linearIndependent c hc⟩,
    fun _ => scalar_identity_mul_transpose c hc,
    fun a => exists_norm_pair_with_paper_factors a c hc⟩

/-- Exact paper-facing statement of Proposition 2.3. -/
theorem paper_euclidean_plane_hyperbolic_basis_exact
    [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    paperHyperbolicPair (K := K) (splitE1 c) (splitE2 c) ∧
      LinearIndependent K ![splitE1 c, splitE2 c] := by
  exact ⟨splitE1_splitE2_hyperbolicPair c hc,
    splitE1_splitE2_linearIndependent c hc⟩

end BuildingUpFormalization.Components.NormForm
