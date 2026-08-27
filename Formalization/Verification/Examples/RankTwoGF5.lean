import Formalization.Components.Foundations
import Formalization.Components.RankBoxedStructure
import Formalization.Components.RankBoxedExtension

/-! Kernel-checked numerical example following Theorem 3.8.
This standalone example does not change the Comparator suite counts. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace BuildingUpFormalization.Verification.Examples.RankTwoGF5

open BuildingUpFormalization
open BuildingUpFormalization.Components.Foundations
open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.RankBoxedExtension

abbrev F := ZMod 5

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def G : Matrix (Fin 4) (Fin 8) F :=
  !![1,3,3,2,1,1,1,3;
     3,4,2,1,4,4,3,2;
     1,4,3,4,2,3,4,2;
     1,2,2,2,3,4,4,4]

def T : Matrix (Fin 4) (Fin 4) F :=
  !![4,1,0,0; 2,1,2,0; 1,3,0,1; 4,0,3,4]

/-- Whole-block order (2,4,1,3), in zero-based Lean indices. -/
def sigma : Fin 4 → Fin 4 := ![1,3,0,2]

def scalarSigma : Fin 8 → Fin 8 := ![2,3,6,7,0,1,4,5]

def Gsigma : Matrix (Fin 4) (Fin 8) F :=
  G.submatrix id scalarSigma

/-- Reversing only the first adjacent pair gives an oriented pairing with
rank-one defect. -/
def rankOneScalarSigma : Fin 8 → Fin 8 := ![1,0,2,3,4,5,6,7]

def GrankOne : Matrix (Fin 4) (Fin 8) F :=
  G.submatrix id rankOneScalarSigma

def rankOneReduction : Matrix (Fin 4) (Fin 4) F :=
  !![0,2,2,0; 2,2,0,0; 1,2,0,0; 1,4,1,1]

def R : Matrix (Fin 4) (Fin 8) F :=
  !![4,4,2,4,2,1,3,3;
     4,3,3,2,2,3,0,2;
     1,2,4,3,1,2,1,2;
     4,3,2,4,1,2,2,4]

def R1 : Matrix (Fin 3) (Fin 6) F :=
  !![3,2,2,3,0,2; 4,3,1,2,1,2; 2,4,1,2,2,4]

def R0 : Matrix (Fin 2) (Fin 4) F :=
  !![1,2,1,2; 1,2,2,4]

def P : Matrix (Fin 2) (Fin 2) F := !![4,2;4,3]
def H : Matrix (Fin 2) (Fin 2) F := !![2,3;2,0]
def Q : Matrix (Fin 2) (Fin 2) F := !![2,2;4,2]
def A : Matrix (Fin 2) (Fin 2) F := !![1,4;4,2]
def D : Matrix (Fin 2) (Fin 2) F := !![1,1;1,2]

/-- Two new pivots added to the SAME rank-two [8,4] matrix. -/
def R3 : Matrix (Fin 5) (Fin 10) F :=
  !![0,1,0,0,1,2,0,0,0,2;
     2,4,4,4,2,4,2,1,3,3;
     2,4,4,3,3,2,2,3,0,2;
     3,1,1,2,4,3,1,2,1,2;
     1,2,4,3,2,4,1,2,2,4]

def R4 : Matrix (Fin 6) (Fin 12) F :=
  !![0,1,0,0,0,0,2,4,0,0,0,2;
     3,1,0,1,0,0,1,2,0,0,0,2;
     2,4,2,4,4,4,2,4,2,1,3,3;
     1,2,2,4,4,3,3,2,2,3,0,2;
     3,1,3,1,1,2,4,3,1,2,1,2;
     1,2,1,2,4,3,2,4,1,2,2,4]

def P3 : Matrix (Fin 3) (Fin 3) F :=
  !![0,0,1;
     2,4,2;
     2,4,3]
def H3 : Matrix (Fin 3) (Fin 2) F :=
  !![0,0;
     2,3;
     2,0]
def Q3 : Matrix (Fin 3) (Fin 2) F :=
  !![0,2;
     2,2;
     4,2]
def A3 : Matrix (Fin 2) (Fin 3) F :=
  !![3,1,4;
     1,4,2]
def P4 : Matrix (Fin 4) (Fin 4) F :=
  !![0,0,0,2;
     3,0,0,1;
     2,2,4,2;
     1,2,4,3]
def H4 : Matrix (Fin 4) (Fin 2) F :=
  !![0,0;
     0,0;
     2,3;
     2,0]
def Q4 : Matrix (Fin 4) (Fin 2) F :=
  !![0,2;
     0,2;
     2,2;
     4,2]
def A4 : Matrix (Fin 2) (Fin 4) F :=
  !![3,3,1,4;
     1,1,4,2]

/-- The new pivot is displayed as (0,1). Swapping just that pair produces
the literal Kim--Lee head (1,0), with the isotropic slope changed from 2 to 3. -/
def swapFirst10 : Fin 10 → Fin 10 := ![1,0,2,3,4,5,6,7,8,9]
def swapFirst12 : Fin 12 → Fin 12 := ![1,0,2,3,4,5,6,7,8,9,10,11]

def x1 : Fin 8 → F := ![0,0,1,2,0,0,0,2]
def x2 : Fin 10 → F := ![0,0,0,0,2,4,0,0,0,2]

/-- Adjacent scalar coordinates are grouped, without any change of form. -/
def blockView {k r : ℕ}
    (M : Matrix (Fin (k + r)) (Fin ((k + r) * 2)) F) :
    RankBoxIndex k r → RankBoxRow F k r :=
  fun i j q => M (finSumFinEquiv i) (finProdFinEquiv (finSumFinEquiv j, q))

def defect {m : ℕ} (M : Matrix (Fin m) (Fin (m * 2)) F) :
    Matrix (Fin m) (Fin m) F :=
  fun i j => M i (finProdFinEquiv (j, (1 : Fin 2))) -
    2 * M i (finProdFinEquiv (j, (0 : Fin 2)))

/-- Every numerical identity printed in the example, including the two
successive restrictions and the rank-two defect presentation. -/
theorem numerical_certificate :
    G * G.transpose = 0 ∧
    Matrix.det (G.submatrix id (Fin.castAdd 4)) = 4 ∧
    Matrix.det T = 3 ∧
    Function.Bijective scalarSigma ∧
    (∀ (j : Fin 4) (q : Fin 2), scalarSigma (finProdFinEquiv (j, q)) =
      finProdFinEquiv (sigma j, q)) ∧
    T * Gsigma = R ∧
    defect G = !![1,1,4,1;3,2,1,1;2,3,4,4;0,3,3,1] ∧
    T * (defect G).submatrix id sigma =
      !![1,0,2,2;0,1,4,2;0,0,0,0;0,0,0,0] ∧
    Function.Bijective rankOneScalarSigma ∧
    Matrix.det rankOneReduction = 4 ∧
    rankOneReduction * defect GrankOne =
      !![1,0,0,0;0,1,0,4;0,0,1,3;0,0,0,0] ∧
    R1 = R.submatrix (fun i => i.succ) (fun j => j.addNat 2) ∧
    R0 = R1.submatrix (fun i => i.succ) (fun j => j.addNat 2) ∧
    Matrix.det D = 1 ∧
    A + D * Q.transpose = 0 ∧
    (1 : Matrix (Fin 2) (Fin 2) F) +
      2 • (P + P.transpose) +
      2 • (H * Q.transpose + Q * H.transpose) + Q * Q.transpose = 0 := by
  decide

private theorem G_independent : LinearIndependent F G := by
  let pi : (Fin 8 → F) →ₗ[F] (Fin 4 → F) :=
    { toFun := fun v j => v (Fin.castAdd 4 j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply LinearIndependent.of_comp pi
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  change Matrix.det (G.submatrix id (Fin.castAdd 4)) ≠ 0
  decide

private theorem G_selfDual : paperSelfDualCode (rowSpace G) := by
  apply paperSelfDualCode_iff_totallyIsotropic_and_finrank_half.mpr
  constructor
  · exact rowSpace_le_orthogonal_of_pairwise_zero (by decide)
  · have hdim : Module.finrank F (rowSpace G) = 4 := by
      simpa [rowSpace] using finrank_span_eq_card G_independent
    simp [hdim, Module.finrank_fintype_fun_eq_card]

private theorem R_form :
    blockView (k := 2) (r := 2) R = rankBoxedRows 2 P H Q A D := by decide

private theorem R1_form :
    blockView (k := 1) (r := 2) R1 =
      rankBoxedRows 2 (!![3]) (!![2,0]) (!![4,2]) (!![4;2]) D := by decide

private theorem R0_form :
    blockView (k := 0) (r := 2) R0 =
      rankBoxedRows 2 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
        (fun i => Fin.elim0 i) (fun _ i => Fin.elim0 i) D := by decide

/-- The dense original code and every displayed retained block code are
Euclidean self-dual. The last two use the SAME terminal matrix D. -/
theorem selfDual_chain :
    paperSelfDualCode (rowSpace G) ∧
    (rankBoxedRowSpace (blockView (k := 2) (r := 2) R) =
      (rankBoxRowBilin (K := F) (k := 2) (r := 2)).orthogonal
        (rankBoxedRowSpace (blockView (k := 2) (r := 2) R))) ∧
    (rankBoxedRowSpace (blockView (k := 1) (r := 2) R1) =
      (rankBoxRowBilin (K := F) (k := 1) (r := 2)).orthogonal
        (rankBoxedRowSpace (blockView (k := 1) (r := 2) R1))) ∧
    (rankBoxedRowSpace (blockView (k := 0) (r := 2) R0) =
      (rankBoxRowBilin (K := F) (k := 0) (r := 2)).orthogonal
        (rankBoxedRowSpace (blockView (k := 0) (r := 2) R0))) := by
  refine ⟨G_selfDual, ?_, ?_, ?_⟩
  · rw [R_form]
    exact (rankBoxedRows_forward_selfDual 2 P H Q A D
      (by decide) (by unfold RankBoxCoreFullRank; decide)
      (by unfold PivotMasterRelations; decide)
      (by unfold PivotGramRelations; decide)).2.2
  · rw [R1_form]
    exact (rankBoxedRows_forward_selfDual 2 (!![3]) (!![2,0]) (!![4,2]) (!![4;2]) D
      (by decide) (by unfold RankBoxCoreFullRank; decide)
      (by unfold PivotMasterRelations; decide)
      (by unfold PivotGramRelations; decide)).2.2
  · rw [R0_form]
    exact (rankBoxedRows_forward_selfDual 2 _ _ _ _ D
      (by decide) (by unfold RankBoxCoreFullRank; decide)
      (by unfold PivotMasterRelations; decide)
      (by unfold PivotGramRelations; decide)).2.2

/-- Both upward steps use the general extension formula, and each is
literally a Kim--Lee building-up matrix after scaling ONLY its first row.
The two simultaneous restrictions return the original [8,4] matrix. -/
theorem extension_numerical_certificate :
    blockView (k := 3) (r := 2) R3 =
      extendedRows 2 P H Q A D ![0,0] ![0,2] ![0,1] ∧
    blockView (k := 3) (r := 2) R3 = rankBoxedRows 2 P3 H3 Q3 A3 D ∧
    blockView (k := 4) (r := 2) R4 =
      extendedRows 2 P3 H3 Q3 A3 D ![0,0] ![0,2] ![0,0,2] ∧
    blockView (k := 4) (r := 2) R4 = rankBoxedRows 2 P4 H4 Q4 A4 D ∧
    defect R4 =
      !![1,0,0,0,0,2;0,1,0,0,0,2;0,0,1,0,2,2;
         0,0,0,1,4,2;0,0,0,0,0,0;0,0,0,0,0,0] ∧
    dot x1 x1 = (-1 : F) ∧ dot x2 x2 = (-1 : F) ∧
    R3.submatrix id swapFirst10 = buildRows x1 3 R ∧
    R4.submatrix id swapFirst12 = buildRows x2 3 R3 ∧
    R3 = R4.submatrix (fun i => i.succ) (fun j => j.addNat 2) ∧
    R = R3.submatrix (fun i => i.succ) (fun j => j.addNat 2) ∧
    R = R4.submatrix (fun i => i.addNat 2) (fun j => j.addNat 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

private theorem scalar_selfDual {n : ℕ}
    (M : Matrix (Fin n) (Fin (2 * n)) F) (cols : Fin n → Fin (2 * n))
    (hdet : Matrix.det (M.submatrix id cols) ≠ 0)
    (horth : ∀ i j, dot (M i) (M j) = 0) :
    paperSelfDualCode (rowSpace M) := by
  let pi : (Fin (2 * n) → F) →ₗ[F] (Fin n → F) :=
    { toFun := fun v j => v (cols j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hli : LinearIndependent F M :=
    LinearIndependent.of_comp pi (Matrix.linearIndependent_rows_of_det_ne_zero hdet)
  apply paperSelfDualCode_iff_totallyIsotropic_and_finrank_half.mpr
  constructor
  · exact rowSpace_le_orthogonal_of_pairwise_zero horth
  · have hdim : Module.finrank F (rowSpace M) = n := by
      simpa [rowSpace] using finrank_span_eq_card hli
    simp [hdim, Module.finrank_fintype_fun_eq_card]

/-- Euclidean self-duality in the original SCALAR coordinates, with
parameters [8,4] -> [10,5] -> [12,6]. -/
theorem buildingUp_chain :
    paperSelfDualCode (rowSpace R) ∧
    paperSelfDualCode (rowSpace R3) ∧
    paperSelfDualCode (rowSpace R4) := by
  refine ⟨?_, ?_, ?_⟩
  · exact scalar_selfDual R ![0,1,2,3] (by decide) (by decide)
  · exact scalar_selfDual R3 ![0,1,2,3,4] (by decide) (by decide)
  · exact scalar_selfDual R4 ![0,1,2,3,4,6] (by decide) (by decide)

#print axioms numerical_certificate
#print axioms selfDual_chain
#print axioms extension_numerical_certificate
#print axioms buildingUp_chain

end BuildingUpFormalization.Verification.Examples.RankTwoGF5
