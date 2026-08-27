import Formalization.Components.Foundations
import Formalization.Components.RankBoxedConstruction
import Formalization.Components.RankBoxedStructure

/-! Kernel-checked algebraic certificate for the large-application baseline.
The MDS distance certificate is the separate exact 3432-minor computation. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

namespace BuildingUpFormalization.Verification.Examples.LargeGF13

open BuildingUpFormalization
open BuildingUpFormalization.Components.Foundations
open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.RankBoxedStructure

abbrev F := ZMod 13

instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- The known pure double-circulant self-dual MDS [14,7,8] code. -/
def M : Matrix (Fin 7) (Fin 14) F :=
  !![1,0,0,0,0,0,0,2,9,10,9,2,1,1;
     0,1,0,0,0,0,0,1,2,9,10,9,2,1;
     0,0,1,0,0,0,0,1,1,2,9,10,9,2;
     0,0,0,1,0,0,0,2,1,1,2,9,10,9;
     0,0,0,0,1,0,0,9,2,1,1,2,9,10;
     0,0,0,0,0,1,0,10,9,2,1,1,2,9;
     0,0,0,0,0,0,1,9,10,9,2,1,1,2]

/-- Coordinate order used by the displayed two-coordinate universal box. -/
def coordinateOrder : Fin 14 → Fin 14 :=
  ![5,10,8,6,11,7,0,1,2,4,3,13,12,9]

theorem coordinateOrder_bijective : Function.Bijective coordinateOrder := by decide

noncomputable def coordinatePerm : Equiv.Perm (Fin 14) :=
  Equiv.ofBijective coordinateOrder coordinateOrder_bijective

noncomputable def Mpaired : Matrix (Fin 7) (Fin 14) F :=
  M.submatrix id coordinatePerm

def T : Matrix (Fin 7) (Fin 7) F :=
  !![12,8,12,5,8,10,0;
     10,11,11,4,3,6,0;
     4,7,2,3,10,9,0;
     9,7,0,9,0,0,0;
     0,0,9,0,7,9,0;
     4,7,0,9,0,5,0;
     0,0,0,0,0,10,7]

def Tinv : Matrix (Fin 7) (Fin 7) F :=
  !![9,7,5,8,0,1,0;
     10,3,8,1,0,1,0;
     9,8,3,0,8,2,0;
     2,8,9,0,0,4,0;
     1,3,12,0,1,10,0;
     9,7,5,0,0,9,0;
     2,3,4,0,0,2,2]

/-- Literal universal rank-one form obtained by exact row normalization. -/
def R : Matrix (Fin 7) (Fin 14) F :=
  !![10,12,0,0,1,5,12,8,12,8,5,12,5,2;
     6,4,5,0,4,7,10,11,11,3,4,7,2,6;
     9,6,0,0,4,8,4,7,2,10,3,2,5,8;
     0,0,0,0,6,4,9,7,0,0,9,6,9,6;
     9,6,0,0,9,6,0,0,9,7,0,0,6,4;
     5,12,0,0,1,5,4,7,0,0,9,7,1,5;
     10,11,4,7,4,7,0,0,0,0,0,0,1,5]

def Parent : Matrix (Fin 6) (Fin 12) F :=
  !![5,0,4,7,10,11,11,3,4,7,2,6;
     0,0,4,8,4,7,2,10,3,2,5,8;
     0,0,6,4,9,7,0,0,9,6,9,6;
     0,0,9,6,0,0,9,7,0,0,6,4;
     0,0,1,5,4,7,0,0,9,7,1,5;
     4,7,4,7,0,0,0,0,0,0,1,5]

def P : Matrix (Fin 6) (Fin 6) F :=
  !![10,0,1,12,12,5;
     6,5,4,10,11,4;
     9,0,4,4,2,3;
     0,0,6,9,0,9;
     9,0,9,0,9,0;
     5,0,1,4,0,9]

def H : Matrix (Fin 6) (Fin 1) F := !![5;2;5;9;6;1]
def Q : Matrix (Fin 6) (Fin 1) F := !![3;9;9;0;0;0]
def A : Matrix (Fin 1) (Fin 6) F := !![10,4,4,0,0,0]
def D : Matrix (Fin 1) (Fin 1) F := !![1]
def gamma : Fin 6 → F := ![6,9,0,9,5,10]

def blockView {k r : ℕ}
    (N : Matrix (Fin (k + r)) (Fin ((k + r) * 2)) F) :
    RankBoxIndex k r → RankBoxRow F k r :=
  fun i j q => N (finSumFinEquiv i) (finProdFinEquiv (finSumFinEquiv j, q))
/-- The published scalar matrix is self-orthogonal. -/
theorem baseline_gram_certificate : M * M.transpose = 0 := by decide

/-- The manuscript's reordered coordinates preserve the Gram condition. -/
theorem paired_gram_certificate : Mpaired * Mpaired.transpose = 0 := by decide

/-- The displayed row operation is invertible and gives the universal rows. -/
theorem normalization_certificate :
    Tinv * T = 1 ∧ T * Tinv = 1 ∧ T * Mpaired = R ∧ Tinv * R = Mpaired := by decide

theorem universal_rows_certificate :
    blockView (k := 6) (r := 1) R = rankBoxedRows 5 P H Q A D := by decide

theorem universal_relations_certificate :
    Matrix.det D = 1 ∧ A + D * Q.transpose = 0 ∧
    (1 : Matrix (Fin 6) (Fin 6) F) +
      5 • (P + P.transpose) +
      5 • (H * Q.transpose + Q * H.transpose) + Q * Q.transpose = 0 := by
  decide

theorem deletion_certificate :
    Parent = R.submatrix (fun i => i.succ) (fun j => j.addNat 2) := by decide

theorem correction_certificate :
    ∀ i, R i.succ 0 = gamma i ∧ R i.succ 1 = 5 * gamma i := by decide

def keepFive : Fin 5 ↪ Fin 6 := ⟨Fin.succ, Fin.succ_injective 5⟩

theorem parent_restriction_certificate :
    blockView (k := 5) (r := 1) Parent =
      restrictRankBoxRows keepFive (blockView (k := 6) (r := 1) R) := by
  decide

/-- Kernel-checked Euclidean self-duality of the MDS baseline and its
two-coordinate deletion parent. -/
theorem selfDual_baseline_and_parent :
    rankBoxedRowSpace (blockView (k := 6) (r := 1) R) =
      (rankBoxRowBilin (K := F) (k := 6) (r := 1)).orthogonal
        (rankBoxedRowSpace (blockView (k := 6) (r := 1) R)) ∧
    rankBoxedRowSpace (blockView (k := 5) (r := 1) Parent) =
      (rankBoxRowBilin (K := F) (k := 5) (r := 1)).orthogonal
        (rankBoxedRowSpace (blockView (k := 5) (r := 1) Parent)) := by
  constructor
  · rw [universal_rows_certificate]
    exact (rankBoxedRows_forward_selfDual 5 P H Q A D
      (by decide) (by unfold RankBoxCoreFullRank; decide)
      (by unfold PivotMasterRelations; decide)
      (by unfold PivotGramRelations; decide)).2.2
  · rw [parent_restriction_certificate, universal_rows_certificate]
    exact (paper_rankBoxed_pivot_restriction_exact keepFive 5 P H Q A D
      (by decide) (by unfold RankBoxCoreFullRank; decide)
      (by unfold PivotMasterRelations; decide)
      (by unfold PivotGramRelations; decide)).2.2.2.2.2

#print axioms baseline_gram_certificate
#print axioms paired_gram_certificate
#print axioms normalization_certificate
#print axioms universal_rows_certificate
#print axioms universal_relations_certificate
#print axioms deletion_certificate
#print axioms correction_certificate
#print axioms parent_restriction_certificate
#print axioms selfDual_baseline_and_parent

end BuildingUpFormalization.Verification.Examples.LargeGF13
