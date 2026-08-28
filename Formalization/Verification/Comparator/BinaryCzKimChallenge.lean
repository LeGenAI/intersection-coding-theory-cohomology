import Formalization.Components.BinaryCzKimDefinitions
import Formalization.Components.Foundations

set_option autoImplicit false

namespace BuildingUpFormalization.Components.BinaryCzKim

open BuildingUpFormalization.Components.Foundations
open LinearMap
open Module

variable {K : Type*} [Field K]

@[simp] theorem binaryDiagonalHead_apply_zero :
    binaryDiagonalHead (K := K) 0 = 1 := by
  sorry

@[simp] theorem binaryDiagonalHead_apply_one :
    binaryDiagonalHead (K := K) 1 = 1 := by
  sorry

theorem standardEuclideanPlaneForm_binaryDiagonalHead_self [CharP K 2] :
    standardEuclideanPlaneForm (K := K) binaryDiagonalHead binaryDiagonalHead = 0 := by
  sorry

theorem standardEuclideanPlaneForm_planeE0_binaryDiagonalHead :
    standardEuclideanPlaneForm (K := K) planeE0 binaryDiagonalHead = 1 := by
  sorry

theorem standardEuclideanPlane_head_not_hyperbolicPair :
    ¬paperHyperbolicPair (K := K) planeE0 binaryDiagonalHead := by
  sorry

theorem dot_r0_riBin_eq_zero_iff [CharP K 2]
    {n : ℕ} (x g : Fin n → K) (y : K) :
    dot (r0 x) (riBin y g) = 0 ↔ y = dot x g := by
  sorry

theorem boxedFamily_coefficient_eq_dot [CharP K 2]
    {m n : ℕ} {x : Fin n → K} {Y : Fin m → K} {G : Fin m → Fin n → K}
    (horth : PairwiseOrthogonal (K := K) (boxedFamily x Y G)) :
    ∀ i : Fin m, Y i = dot x (G i) := by
  sorry

theorem dot_riBin_riBin_eq_dot [CharP K 2]
    {n : ℕ} (g h : Fin n → K) (y z : K) :
    dot (riBin y g) (riBin z h) = dot g h := by
  sorry

theorem boxedFamily_tail_pairwiseOrthogonal [CharP K 2]
    {m n : ℕ} {x : Fin n → K} {Y : Fin m → K} {G : Fin m → Fin n → K}
    (horth : PairwiseOrthogonal (K := K) (boxedFamily x Y G)) :
    PairwiseOrthogonal (K := K) G := by
  sorry

@[simp] theorem buildSuccBinLinear_apply
    {n : ℕ} (x g : Fin n → K) :
    buildSuccBinLinear x g = riBin (dot x g) g := by
  sorry

theorem buildRowsBin_succ_eq_buildSuccBinLinear
    {m n : ℕ} (x : Fin n → K) (G : Fin m → Fin n → K) (i : Fin m) :
    buildRowsBin x G (Fin.succ i) = buildSuccBinLinear x (G i) := by
  sorry

theorem buildRowsBin_tail_linearIndependent
    {m n : ℕ} {x : Fin n → K} {G : Fin m → Fin n → K}
    (hbuild : LinearIndependent K (buildRowsBin x G)) :
    LinearIndependent K G := by
  sorry

theorem buildRows_one_eq_buildRowsBin [CharP K 2]
    {m n : ℕ} (x : Fin n → K) (G : Fin m → Fin n → K) :
    buildRows x 1 G = buildRowsBin x G := by
  sorry

theorem paper_binary_kim_building_up_exact [CharP K 2]
    {m : ℕ} {x : Fin (2 * m) → K}
    {G : Fin m → Fin (2 * m) → K}
    (hx : dot x x = (1 : K))
    (hparent : paperSelfDualCode (K := K) (rowSpace G)) :
    paperSelfDualCode (K := K) (rowSpace (buildRowsBin x G)) := by
  sorry

theorem isSelfOrthogonal_map_of_isFormIsometry
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {Bᵥ : LinearMap.BilinForm K V} {B𝓌 : LinearMap.BilinForm K W}
    {e : V ≃ₗ[K] W} {L : Submodule K V}
    (he : IsFormIsometry Bᵥ B𝓌 e) (hL : IsSelfOrthogonal Bᵥ L) :
    IsSelfOrthogonal B𝓌 (L.map e.toLinearMap) := by
  sorry

theorem boxedFamily_linearIndependent_of_paperSelfDualCode
    {m : ℕ} {x : Fin (2 * m) → K} {Y : Fin m → K}
    {G : Fin m → Fin (2 * m) → K}
    (hself : paperSelfDualCode (K := K) (rowSpace (boxedFamily x Y G))) :
    LinearIndependent K (boxedFamily x Y G) := by
  sorry

theorem boxedFamily_tail_paperSelfDualCode [CharP K 2]
    {m : ℕ} {x : Fin (2 * m) → K} {Y : Fin m → K}
    {G : Fin m → Fin (2 * m) → K}
    (hself : paperSelfDualCode (K := K) (rowSpace (boxedFamily x Y G))) :
    paperSelfDualCode (K := K) (rowSpace G) := by
  sorry

theorem paper_binary_cz_kim_corrected [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module K V]
    {m : ℕ} {Bcoh : LinearMap.BilinForm K V} {L : Submodule K V}
    (e : V ≃ₗ[K] (Fin (2 + 2 * m) → K))
    (he : IsFormIsometry Bcoh (dotBilin (K := K) (n := 2 + 2 * m)) e)
    (hL : IsSelfOrthogonal Bcoh L)
    {x : Fin (2 * m) → K} {Y : Fin m → K}
    {G : Fin m → Fin (2 * m) → K}
    (hcode : L.map e.toLinearMap = rowSpace (boxedFamily x Y G)) :
    IsSelfOrthogonal (dotBilin (K := K) (n := 2 + 2 * m)) (L.map e.toLinearMap) ∧
      dot x x = (1 : K) ∧
      paperSelfDualCode (K := K) (rowSpace G) ∧
      (∀ i : Fin m, Y i = dot x (G i)) ∧
      boxedFamily x Y G = buildRowsBin x G ∧
      deleteBinaryHeadPair (boxedFamily x Y G) = G ∧
      CodeEquiv (buildRowsBin x (deleteBinaryHeadPair (boxedFamily x Y G)))
        (boxedFamily x Y G) := by
  sorry

end BuildingUpFormalization.Components.BinaryCzKim
