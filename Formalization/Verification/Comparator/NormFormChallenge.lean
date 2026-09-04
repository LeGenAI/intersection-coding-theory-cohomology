import Formalization.Archive.SubmittedBaseline

set_option autoImplicit false

namespace BuildingUpFormalization.Components.NormForm

variable {K : Type*} [Field K]

theorem root_neg_one_orderOf
    [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    orderOf c = 4 := by
  sorry

theorem scalar_identity_mul_transpose
    {k : ℕ} (c : K) (hc : c ^ 2 = (-1 : K)) :
    (c • (1 : Matrix (Fin k) (Fin k) K)) *
        (c • (1 : Matrix (Fin k) (Fin k) K)).transpose =
      -(1 : Matrix (Fin k) (Fin k) K) := by
  sorry

theorem splitE1_splitE2_hyperbolicPair
    [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    paperHyperbolicPair (K := K) (splitE1 c) (splitE2 c) := by
  sorry

theorem splitE1_splitE2_linearIndependent
    [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    LinearIndependent K ![splitE1 c, splitE2 c] := by
  sorry

theorem norm_form_splitting_paper_order
    (c x y : K) (hc : c ^ 2 = (-1 : K)) :
    x ^ 2 + y ^ 2 = (x - c * y) * (x + c * y) := by
  sorry

theorem norm_form_witness_factors
    [Fact ((2 : K) ≠ 0)] (a c : K) (hc : c ^ 2 = (-1 : K)) :
    let x : K := (1 + a) / 2
    let y : K := ((1 - a) / 2) * c
    x - c * y = 1 ∧ x + c * y = a ∧ x ^ 2 + y ^ 2 = a := by
  sorry

theorem exists_norm_pair_with_paper_factors
    [Fact ((2 : K) ≠ 0)] (a c : K) (hc : c ^ 2 = (-1 : K)) :
    ∃ x y : K,
      x - c * y = 1 ∧ x + c * y = a ∧ x ^ 2 + y ^ 2 = a := by
  sorry

theorem paper_split_consequences_exact
    [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    orderOf c = 4 ∧
      (∀ k : ℕ,
        (c • (1 : Matrix (Fin k) (Fin k) K)) *
            (c • (1 : Matrix (Fin k) (Fin k) K)).transpose =
          -(1 : Matrix (Fin k) (Fin k) K)) ∧
      (∀ a : K, ∃ x y : K,
        x - c * y = 1 ∧ x + c * y = a ∧ x ^ 2 + y ^ 2 = a) := by
  sorry

theorem paper_euclidean_plane_hyperbolic_basis_exact
    [Fact ((2 : K) ≠ 0)] (c : K) (hc : c ^ 2 = (-1 : K)) :
    paperHyperbolicPair (K := K) (splitE1 c) (splitE2 c) ∧
      LinearIndependent K ![splitE1 c, splitE2 c] := by
  sorry

end BuildingUpFormalization.Components.NormForm
