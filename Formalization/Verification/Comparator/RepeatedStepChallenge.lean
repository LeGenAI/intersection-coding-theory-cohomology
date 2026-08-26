import Formalization.Components.RepeatedStepDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RepeatedStep

variable {K : Type*} [Field K]

theorem one_step_normalization_exact {m n : ℕ} (c p : K) (rho : Fin n → K)
    (gamma : Fin m → K) (G : Matrix (Fin m) (Fin n) K)
    (hc : c ^ 2 = (-1 : K))
    (hG : paperSelfDualCode (rowSpace G))
    (hB : paperSelfDualCode (rowSpace (borderedRows c p rho gamma G)))
    (s : Fin m) (hs : gamma s ≠ 0) :
    let x := normalizedTail c p rho gamma G s
    dot x x = -1 ∧ (∀ i, dot x (G i) = -gamma i) ∧
    normalizedBorder c p rho gamma G s = buildRows x c G ∧
    rowSpace (borderedRows c p rho gamma G) = rowSpace (buildRows x c G) ∧
    (∀ i j, buildRows x c G i.succ (Fin.natAdd 2 j) = G i j) := by
  sorry

theorem zero_column_exact {m n : ℕ} (c p : K) (rho : Fin n → K)
    (G : Matrix (Fin m) (Fin n) K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hG : paperSelfDualCode (rowSpace G))
    (hB : paperSelfDualCode (rowSpace (borderedRows c p rho 0 G))) :
    p = c / 2 ∧ rho ∈ rowSpace G ∧
    rowSpace (borderedRows c p rho 0 G) = rowSpace (directSumRows c G) ∧
    ∀ x, rowSpace (borderedRows c p rho 0 G) ≠ rowSpace (buildRows x c G) := by
  sorry

theorem one_step_kim_lee_iff {m n : ℕ} (c p : K) (rho : Fin n → K)
    (gamma : Fin m → K) (G : Matrix (Fin m) (Fin n) K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hG : paperSelfDualCode (rowSpace G))
    (hB : paperSelfDualCode (rowSpace (borderedRows c p rho gamma G))) :
    (∃ x, dot x x = -1 ∧
      rowSpace (borderedRows c p rho gamma G) = rowSpace (buildRows x c G)) ↔
      gamma ≠ 0 := by
  sorry

theorem binary_normalization_exact {m n : ℕ} [CharP K 2]
    (rho : Fin n → K) (gamma : Fin m → K) (G : Matrix (Fin m) (Fin n) K)
    (hG : paperSelfDualCode (rowSpace G))
    (hB : paperSelfDualCode (rowSpace (borderedRows 1 0 rho gamma G)))
    (s : Fin m) (hs : gamma s = 1) :
    normalizedTail 1 0 rho gamma G s = rho + G s ∧
    normalizedBorder 1 0 rho gamma G s = buildRowsBin (rho + G s) G ∧
    dot (rho + G s) (rho + G s) = 1 ∧
    rowSpace (borderedRows 1 0 rho gamma G) = rowSpace (buildRowsBin (rho + G s) G) := by
  sorry

end BuildingUpFormalization.Components.RepeatedStep
