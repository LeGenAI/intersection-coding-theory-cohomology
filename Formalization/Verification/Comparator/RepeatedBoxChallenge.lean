import Formalization.Components.RepeatedBoxDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RepeatedBox

open BuildingUpFormalization.Components.SplitBoxed
open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.RankBoxedStructure
open BuildingUpFormalization.Components.RankBoxedExtension
open BuildingUpFormalization.Components.RepeatedStep

variable {K : Type*} [Field K]

theorem extension_dictionary_exact {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (h q : Fin r → K) (u : Fin k → K) :
    readSuccessor (extendedRows c P H Q A D h q u) =
      borderedRows c (c / 2 * (1 + ∑ t, q t * q t) - ∑ t, h t * q t)
        (flattenRow (extensionTail c h q u))
        (fun i => extensionGamma c H Q D h q u (finSumFinEquiv.symm i))
        (flattenRows (rankBoxedRows c P H Q A D)) := by
  sorry

theorem extension_zero_column_iff {k r : ℕ} (c : K)
    (H Q : Fin k → Fin r → K) (D : Fin r → Fin r → K)
    (hD : RankBoxCoreFullRank D) (h q : Fin r → K) (u : Fin k → K) :
    extensionGamma c H Q D h q u = 0 ↔
      q = 0 ∧ ∀ i, u i = -(∑ t, Q i t * h t) := by
  sorry

theorem repeated_step_selfDual_exact {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D) (hpp : PivotGramRelations c P H Q)
    (h q : Fin r → K) (u : Fin k → K) :
    paperSelfDualCode (rowSpace (flattenRows (rankBoxedRows c P H Q A D))) ∧
    paperSelfDualCode (rowSpace (readSuccessor (extendedRows c P H Q A D h q u))) := by
  sorry

theorem repeated_step_normalization_exact {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D) (hpp : PivotGramRelations c P H Q)
    (h q : Fin r → K) (u : Fin k → K) (s : Fin (k + r))
    (hs : extensionGamma c H Q D h q u (finSumFinEquiv.symm s) ≠ 0) :
    let p := c / 2 * (1 + ∑ t, q t * q t) - ∑ t, h t * q t
    let rho := flattenRow (extensionTail c h q u)
    let gamma := fun i => extensionGamma c H Q D h q u (finSumFinEquiv.symm i)
    let G := flattenRows (rankBoxedRows c P H Q A D)
    let x := normalizedTail c p rho gamma G s
    dot x x = -1 ∧ (∀ i, dot x (G i) = -gamma i) ∧
      topRowOperation c⁻¹ (Pi.single s (c⁻¹ * normalizingCoeff c p gamma s))
        (readSuccessor (extendedRows c P H Q A D h q u)) = buildRows x c G ∧
      rowSpace (readSuccessor (extendedRows c P H Q A D h q u)) =
        rowSpace (buildRows x c G) ∧
      (∀ i j, buildRows x c G i.succ (Fin.natAdd 2 j) = G i j) := by
  sorry

theorem repeated_step_kim_lee_iff {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D) (hpp : PivotGramRelations c P H Q)
    (h q : Fin r → K) (u : Fin k → K) :
    (∃ x, dot x x = -1 ∧
      rowSpace (readSuccessor (extendedRows c P H Q A D h q u)) =
        rowSpace (buildRows x c (flattenRows (rankBoxedRows c P H Q A D)))) ↔
      ¬ (q = 0 ∧ ∀ i, u i = -(∑ t, Q i t * h t)) := by
  sorry

theorem kim_lee_to_repeated_exact {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D) (hpp : PivotGramRelations c P H Q)
    (x : Fin ((k + r) * 2) → K) (hx : dot x x = -1) :
    let G := flattenRows (rankBoxedRows c P H Q A D)
    let rho := reverseTail c P H Q A D x
    let h := fun t => rho (.inr t) 0
    let q := fun t => blockDefect c (rho (.inr t))
    let u := fun j => rho (.inl j) 0
    readSuccessor (extendedRows c P H Q A D h q u) =
        topRowOperation c (reverseCoeff c x) (buildRows x c G) ∧
      rowSpace (readSuccessor (extendedRows c P H Q A D h q u)) =
        rowSpace (buildRows x c G) ∧
      extensionGamma c H Q D h q u ≠ 0 ∧
      restrictRankBoxRows (Fin.succEmb k) (extendedRows c P H Q A D h q u) =
        rankBoxedRows c P H Q A D := by
  sorry

end BuildingUpFormalization.Components.RepeatedBox
