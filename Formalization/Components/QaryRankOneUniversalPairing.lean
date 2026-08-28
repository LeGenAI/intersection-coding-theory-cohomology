import Formalization.Components.QaryRankOnePairingMerge
import Formalization.Components.RepeatedBox
import Formalization.Components.QaryRankBoxedNormalization

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryRankOneUniversalPairing

open Set Submodule
open BuildingUpFormalization.Components.Foundations
open BuildingUpFormalization.Components.QaryRankBoxedNormalization
open BuildingUpFormalization.Components.QaryRankOneOrientedPairing
open BuildingUpFormalization.Components.QaryRankOnePairingMerge
open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.RankBoxedStructure
open BuildingUpFormalization.Components.RankBoxedExtension
open BuildingUpFormalization.Components.RepeatedBox
open BuildingUpFormalization.Components.RepeatedStep

variable {K : Type*} [Field K]

/-- Exact composition law for whole-block relabellings. -/
theorem relabelBlockCode_trans_exact {ι κ μ : Type*}
    (σ : ι ≃ κ) (τ : κ ≃ μ)
    (C : Submodule K (QaryBlockRow K μ)) :
    relabelBlockCode (K := K) σ (relabelBlockCode (K := K) τ C) =
      relabelBlockCode (K := K) (σ.trans τ) C := by
  unfold relabelBlockCode
  rw [← Submodule.map_comp]
  congr 1

/-- Whole-block relabelling preserves the rank-one oriented-pairing property
even when the two finite index types use different cardinal expressions. -/
theorem hasQaryRankOneOrientedPairing_relabelBlockCode_fin_iff
    {m n : ℕ} (c : K) (σ : Fin m ≃ Fin n)
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    HasQaryRankOneOrientedPairing c (relabelBlockCode (K := K) σ C) ↔
      HasQaryRankOneOrientedPairing c C := by
  have hmn : m = n := by
    simpa using Fintype.card_congr σ
  subst n
  exact hasQaryRankOneOrientedPairing_relabelBlockCode_iff c σ C

/-- Read a scalar child row space with the new block first.  This convention
matches `readSuccessor` and `flattenRows` literally. -/
def frontPrependedScalarRowSpaceAsBlock {m n : ℕ}
    (B : Matrix (Fin m) (Fin (2 + n * 2)) K) :
    Submodule K (QaryBlockRow K (Fin (n + 1))) :=
  relabelBlockCode (K := K) (finSuccEquiv n)
    (prependedScalarRowSpaceAsBlock (K := K) B)

/-- Read a scalar child row space in standard `Fin (n+1)` block indexing. -/
def finPrependedScalarRowSpaceAsBlock {m n : ℕ}
    (B : Matrix (Fin m) (Fin (2 + n * 2)) K) :
    Submodule K (QaryBlockRow K (Fin (n + 1))) :=
  relabelBlockCode (K := K) finSuccEquivLast
    (prependedScalarRowSpaceAsBlock (K := K) B)

/-- The front-first and last-new readings differ by one explicit whole-block
permutation. -/
theorem frontPrepended_eq_relabel_finPrepended {m n : ℕ}
    (B : Matrix (Fin m) (Fin (2 + n * 2)) K) :
    frontPrependedScalarRowSpaceAsBlock (K := K) B =
      relabelBlockCode (K := K)
        ((finSuccEquiv n).trans finSuccEquivLast.symm)
        (finPrependedScalarRowSpaceAsBlock (K := K) B) := by
  unfold frontPrependedScalarRowSpaceAsBlock
    finPrependedScalarRowSpaceAsBlock
  rw [relabelBlockCode_trans_exact]
  congr 1
  apply Equiv.ext
  intro i
  simp

/-- `finPrependedScalarRowSpaceAsBlock` depends only on the scalar row
space, not on the chosen generating rows. -/
theorem finPrependedScalarRowSpaceAsBlock_congr {m₁ m₂ n : ℕ}
    (B₁ : Matrix (Fin m₁) (Fin (2 + n * 2)) K)
    (B₂ : Matrix (Fin m₂) (Fin (2 + n * 2)) K)
    (h : rowSpace B₁ = rowSpace B₂) :
    finPrependedScalarRowSpaceAsBlock (K := K) B₁ =
      finPrependedScalarRowSpaceAsBlock (K := K) B₂ := by
  unfold finPrependedScalarRowSpaceAsBlock prependedScalarRowSpaceAsBlock
  rw [h]

/-- Finite-index row-space dictionary for the literal building-up branch. -/
theorem finPrependedScalarRowSpace_buildRows_exact
    {m n : ℕ} (x : Fin (n * 2) → K) (c : K)
    (G : Matrix (Fin m) (Fin (n * 2)) K) :
    finPrependedScalarRowSpaceAsBlock (K := K) (buildRows x c G) =
      finBuildingUpBlockCode (K := K) c (scalarRowSpaceAsBlock G)
        (finScalarBlockLinearEquiv (K := K) x)
        (blockDotFunctional x (scalarRowSpaceAsBlock G)) := by
  unfold finPrependedScalarRowSpaceAsBlock finBuildingUpBlockCode
  rw [prependedScalarRowSpace_buildRows_eq_buildingUpBlockCode_exact]

/-- Finite-index row-space dictionary for the literal direct-sum branch. -/
theorem finPrependedScalarRowSpace_directSumRows_exact
    {m n : ℕ} (c : K) (G : Matrix (Fin m) (Fin (n * 2)) K) :
    finPrependedScalarRowSpaceAsBlock (K := K) (directSumRows c G) =
      finDirectSumBlockCode (K := K) (-c) (scalarRowSpaceAsBlock G) := by
  unfold finPrependedScalarRowSpaceAsBlock finDirectSumBlockCode
  rw [prependedScalarRowSpace_directSumRows_exact]

/-- Grouping the consecutive scalar coordinates of `flattenRows` recovers
the rank-box row space, with the canonical `Fin (k+r)` block indexing. -/
theorem scalarRowSpaceAsBlock_flattenRows_exact {k r : ℕ}
    (R : RankBoxIndex k r → RankBoxRow K k r) :
    scalarRowSpaceAsBlock (K := K) (flattenRows R) =
      relabelBlockCode (K := K) finSumFinEquiv.symm
        (rankBoxedRowSpace R) := by
  unfold scalarRowSpaceAsBlock rowSpace relabelBlockCode rankBoxedRowSpace
  rw [Submodule.map_span, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
    refine ⟨R (finSumFinEquiv.symm i),
      ⟨finSumFinEquiv.symm i, rfl⟩, ?_⟩
    funext j q
    simp [finScalarBlockLinearEquiv, blockRelabelLinearEquiv,
      flattenRows, flattenRow]
  · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
    refine ⟨flattenRows R (finSumFinEquiv i),
      ⟨finSumFinEquiv i, rfl⟩, ?_⟩
    funext j q
    simp [finScalarBlockLinearEquiv, blockRelabelLinearEquiv,
      flattenRows, flattenRow]

/-- Insert the first pivot before the restricted parent indices. -/
def frontOptionRankBoxEquiv (k r : ℕ) :
    Option (RankBoxIndex k r) ≃ RankBoxIndex (k + 1) r where
  toFun
    | none => .inl 0
    | some (.inl i) => .inl i.succ
    | some (.inr t) => .inr t
  invFun
    | .inl i => Fin.cases none (fun j => some (.inl j)) i
    | .inr t => some (.inr t)
  left_inv x := by cases x with | none => rfl | some x => cases x <;> rfl
  right_inv x := by
    cases x with
    | inl i => exact Fin.cases rfl (fun _ => rfl) i
    | inr t => rfl

/-- Canonical block order used by `readSuccessor`: the new pivot first,
followed by the restricted pivot and terminal indices. -/
def frontRankBoxEquiv (k r : ℕ) :
    Fin (k + r + 1) ≃ RankBoxIndex (k + 1) r :=
  (finSuccEquiv (k + r)).trans
    ((Equiv.optionCongr finSumFinEquiv.symm).trans
      (frontOptionRankBoxEquiv k r))

/-- Reading the first pivot as a front-prepended scalar block recovers the
full rank-box row space under the canonical whole-block permutation. -/
theorem frontPrepended_readSuccessor_eq_rankBoxedRowSpace_exact {k r : ℕ}
    (R : RankBoxIndex (k + 1) r → RankBoxRow K (k + 1) r) :
    frontPrependedScalarRowSpaceAsBlock (K := K) (readSuccessor R) =
      relabelBlockCode (K := K) (frontRankBoxEquiv k r)
        (rankBoxedRowSpace R) := by
  have hfront_zero : frontRankBoxEquiv k r 0 =
      (Sum.inl 0 : RankBoxIndex (k + 1) r) := by
    simp [frontRankBoxEquiv, frontOptionRankBoxEquiv, Equiv.optionCongr]
  have hfront_succ (i : Fin (k + r)) :
      frontRankBoxEquiv k r i.succ =
        keepRankBoxIndex (Fin.succEmb k) (finSumFinEquiv.symm i) := by
    simp only [frontRankBoxEquiv, Equiv.trans_apply, finSuccEquiv_succ]
    simp [Equiv.optionCongr]
    cases finSumFinEquiv.symm i <;> rfl
  have hgen (i : Fin (k + r + 1)) :
      ((blockRelabelLinearEquiv (K := K) (finSuccEquiv (k + r))).toLinearMap.comp
        (prependedScalarBlockLinearEquiv (K := K)).toLinearMap)
          (readSuccessor R i) =
      blockRelabelLinearEquiv (K := K) (frontRankBoxEquiv k r)
        (R (frontRankBoxEquiv k r i)) := by
    refine Fin.cases ?_ (fun i => ?_) i <;>
      funext j q <;> refine Fin.cases ?_ (fun j => ?_) j <;> fin_cases q <;>
      simp [LinearMap.comp_apply, blockRelabelLinearEquiv,
        prependedScalarBlockLinearEquiv, readSuccessor, flattenRow, prepend2,
        head2, hfront_zero, hfront_succ]
  unfold frontPrependedScalarRowSpaceAsBlock prependedScalarRowSpaceAsBlock
    rowSpace relabelBlockCode rankBoxedRowSpace
  rw [← Submodule.map_comp, Submodule.map_span, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
    refine ⟨R (frontRankBoxEquiv k r i),
      ⟨frontRankBoxEquiv k r i, rfl⟩, (hgen i).symm⟩
  · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
    refine ⟨readSuccessor R ((frontRankBoxEquiv k r).symm i),
      ⟨(frontRankBoxEquiv k r).symm i, rfl⟩, ?_⟩
    simpa using hgen ((frontRankBoxEquiv k r).symm i)

/-- Scalar consecutive-pair grouping and the front-first successor reading
are the same code under the explicit whole-block reindexing. -/
theorem frontPrepended_readSuccessor_eq_relabel_flattenRows_exact {k r : ℕ}
    (R : RankBoxIndex (k + 1) r → RankBoxRow K (k + 1) r) :
    frontPrependedScalarRowSpaceAsBlock (K := K) (readSuccessor R) =
      relabelBlockCode (K := K)
        ((frontRankBoxEquiv k r).trans finSumFinEquiv)
        (scalarRowSpaceAsBlock (K := K) (flattenRows R)) := by
  rw [frontPrepended_readSuccessor_eq_rankBoxedRowSpace_exact,
    scalarRowSpaceAsBlock_flattenRows_exact,
    relabelBlockCode_trans_exact]
  congr 1
  apply Equiv.ext
  intro i
  simp

/-- The first direct-sum step from the zero-length isotropic-line code is
already the one-block isotropic-line code after swapping its two new scalar
coordinates. -/
theorem finDirectSumBlockCode_neg_empty_has_rankOne_exact
    (c : K) (hc : c ^ 2 = (-1 : K)) :
    HasQaryRankOneOrientedPairing c
      (finDirectSumBlockCode (K := K) (-c)
        (qaryIsotropicLineCode (K := K) (ι := Fin 0) c)) := by
  apply (hasQaryRankOneOrientedPairing_scalarCoordinatePermuted_iff
    c finLastBlockScalarSwap
      (finDirectSumBlockCode (K := K) (-c)
        (qaryIsotropicLineCode (K := K) (ι := Fin 0) c))).mp
  rw [finLastSwap_directSumBlockCode_neg_exact c _ hc,
    finDirectSumBlockCode_qaryIsotropicLineCode_exact]
  exact qaryIsotropicLineCode_has_rankOne_orientedPairing_exact
    (K := K) (n := 1) (by omega) c hc

/-- One exact rank-box successor preserves existence of a rank-one oriented
pairing.  The two cases are supplied by the exhaustive literal row-space
dichotomy; no choice of branch is hidden in the statement. -/
theorem repeated_step_has_rankOne_orientedPairing_exact {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D) (hpp : PivotGramRelations c P H Q)
    (h q : Fin r → K) (u : Fin k → K)
    (hparent : HasQaryRankOneOrientedPairing c
      (scalarRowSpaceAsBlock
        (flattenRows (rankBoxedRows c P H Q A D)))) :
    HasQaryRankOneOrientedPairing c
      (finPrependedScalarRowSpaceAsBlock (K := K)
        (readSuccessor (extendedRows c P H Q A D h q u))) := by
  have hc0 : c ≠ 0 := by
    intro hz
    simp [hz] at hc
  let G := flattenRows (rankBoxedRows c P H Q A D)
  have hboxed := rankBoxedRows_forward_selfDual c P H Q A D
    (by simpa [pow_two] using hc) hD hpm hpp
  have hli : LinearIndependent K G := by
    exact flattenRows_linearIndependent _ hboxed.2.1
  have hrowfin : Module.finrank K (rowSpace G) = k + r := by
    simpa [G, rowSpace] using finrank_span_eq_card hli
  have hsquare : Module.finrank K (scalarRowSpaceAsBlock G) = k + r := by
    unfold scalarRowSpaceAsBlock
    rw [(finScalarBlockLinearEquiv (K := K) (n := k + r)).finrank_map_eq]
    exact hrowfin
  rcases repeated_step_rowSpace_dichotomy_exact
      c P H Q A D hc h2 hD hpm hpp h q u with hbuild | hdirect
  · obtain ⟨x, hx, hrows⟩ := hbuild
    have hcode := finPrependedScalarRowSpaceAsBlock_congr
      (K := K) (readSuccessor (extendedRows c P H Q A D h q u))
        (buildRows x c G) (by simpa [G] using hrows)
    rw [hcode, finPrependedScalarRowSpace_buildRows_exact]
    exact finBuildingUpBlockCode_has_rankOne_orientedPairing_of_parent_exact
      c (scalarRowSpaceAsBlock G)
        (finScalarBlockLinearEquiv (K := K) x)
        (blockDotFunctional x (scalarRowSpaceAsBlock G)) hc0 hparent
  · have hcode := finPrependedScalarRowSpaceAsBlock_congr
      (K := K) (readSuccessor (extendedRows c P H Q A D h q u))
        (directSumRows c G) (by simpa [G] using hdirect)
    rw [hcode, finPrependedScalarRowSpace_directSumRows_exact]
    exact finDirectSumBlockCode_neg_has_rankOne_orientedPairing_of_parent_exact
      c (scalarRowSpaceAsBlock G) hc hsquare hparent

/-- Front-first form of the preceding successor theorem, matching the block
order of the full rank-box matrix. -/
theorem repeated_step_front_has_rankOne_orientedPairing_exact
    {k r : ℕ} (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D) (hpp : PivotGramRelations c P H Q)
    (h q : Fin r → K) (u : Fin k → K)
    (hparent : HasQaryRankOneOrientedPairing c
      (scalarRowSpaceAsBlock
        (flattenRows (rankBoxedRows c P H Q A D)))) :
    HasQaryRankOneOrientedPairing c
      (frontPrependedScalarRowSpaceAsBlock (K := K)
        (readSuccessor (extendedRows c P H Q A D h q u))) := by
  have hlast := repeated_step_has_rankOne_orientedPairing_exact
    c P H Q A D hc h2 hD hpm hpp h q u hparent
  rw [frontPrepended_eq_relabel_finPrepended]
  exact (hasQaryRankOneOrientedPairing_relabelBlockCode_iff
    c ((finSuccEquiv (k + r)).trans finSuccEquivLast.symm)
      (finPrependedScalarRowSpaceAsBlock (K := K)
        (readSuccessor (extendedRows c P H Q A D h q u)))).mpr hlast

/-- Every nonempty valid rank-box normal form admits a rank-one oriented
coordinate pairing.  The proof removes the first pivot recursively and uses
the exact building-up/direct-sum dichotomy at every reconstruction step. -/
theorem rankBoxed_flatten_has_rankOne_orientedPairing_exact
    {k r : ℕ} (hn : 0 < k + r) (c : K)
    (P : Fin k → Fin k → K) (H Q : Fin k → Fin r → K)
    (A : Fin r → Fin k → K) (D : Fin r → Fin r → K)
    (hc : c ^ 2 = (-1 : K)) (h2 : (2 : K) ≠ 0)
    (hD : RankBoxCoreFullRank D)
    (hpm : PivotMasterRelations Q A D)
    (hpp : PivotGramRelations c P H Q) :
    HasQaryRankOneOrientedPairing c
      (scalarRowSpaceAsBlock
        (flattenRows (rankBoxedRows c P H Q A D))) := by
  induction k with
  | zero =>
      rw [scalarRowSpaceAsBlock_flattenRows_exact,
        paper_rankBoxed_terminal_exact c P H Q A D hD,
        relabelBlockCode_qaryIsotropicLineCode_exact]
      exact qaryIsotropicLineCode_has_rankOne_orientedPairing_exact
        (K := K) (n := 0 + r) hn c hc
  | succ k ih =>
      let P' : Fin k → Fin k → K := fun i j => P i.succ j.succ
      let H' : Fin k → Fin r → K := fun i t => H i.succ t
      let Q' : Fin k → Fin r → K := fun i t => Q i.succ t
      let A' : Fin r → Fin k → K := fun t j => A t j.succ
      have hpm' : PivotMasterRelations Q' A' D := by
        intro s i
        exact hpm s i.succ
      have hpp' : PivotGramRelations c P' H' Q' := by
        intro i j
        simpa [P', H', Q'] using hpp i.succ j.succ
      have hdict := paper_rankBoxed_successor_dictionary_exact
        c P H Q A D hc h2 hpm hpp
      by_cases hparent_nonempty : 0 < k + r
      · have hparent := ih hparent_nonempty P' H' Q' A'
          hpm' hpp'
        have hfront := repeated_step_front_has_rankOne_orientedPairing_exact
          c P' H' Q' A' D hc h2 hD hpm' hpp'
            (H 0) (Q 0) (fun j => P 0 j.succ) hparent
        rw [← hdict,
          frontPrepended_readSuccessor_eq_relabel_flattenRows_exact] at hfront
        exact (hasQaryRankOneOrientedPairing_relabelBlockCode_fin_iff
          c ((frontRankBoxEquiv k r).trans finSumFinEquiv)
            (scalarRowSpaceAsBlock
              (flattenRows (rankBoxedRows c P H Q A D)))).mp hfront
      · have hk : k = 0 := by omega
        have hr : r = 0 := by omega
        subst k
        subst r
        have hdirect :
            rowSpace (readSuccessor
              (extendedRows c P' H' Q' A' D
                (H 0) (Q 0) (fun j => P 0 j.succ))) =
              rowSpace (directSumRows c
                (flattenRows (rankBoxedRows c P' H' Q' A' D))) := by
          rcases repeated_step_rowSpace_dichotomy_exact
              c P' H' Q' A' D hc h2 hD hpm' hpp'
                (H 0) (Q 0) (fun j => P 0 j.succ) with hbuild | hdirect
          · obtain ⟨x, hx, _⟩ := hbuild
            simp [dot] at hx
          · exact hdirect
        have hparent_code :
            scalarRowSpaceAsBlock
                (flattenRows (rankBoxedRows c P' H' Q' A' D)) =
              qaryIsotropicLineCode (K := K) (ι := Fin 0) c := by
          rw [scalarRowSpaceAsBlock_flattenRows_exact,
            paper_rankBoxed_terminal_exact c P' H' Q' A' D hD,
            relabelBlockCode_qaryIsotropicLineCode_exact]
        have hlast : HasQaryRankOneOrientedPairing c
            (finPrependedScalarRowSpaceAsBlock (K := K)
              (readSuccessor
                (extendedRows c P' H' Q' A' D
                  (H 0) (Q 0) (fun j => P 0 j.succ)))) := by
          rw [finPrependedScalarRowSpaceAsBlock_congr
              (K := K)
              (readSuccessor
                (extendedRows c P' H' Q' A' D
                  (H 0) (Q 0) (fun j => P 0 j.succ)))
              (directSumRows c
                (flattenRows (rankBoxedRows c P' H' Q' A' D))) hdirect,
            finPrependedScalarRowSpace_directSumRows_exact,
            hparent_code]
          exact finDirectSumBlockCode_neg_empty_has_rankOne_exact c hc
        have hfront : HasQaryRankOneOrientedPairing c
            (frontPrependedScalarRowSpaceAsBlock (K := K)
              (readSuccessor
                (extendedRows c P' H' Q' A' D
                  (H 0) (Q 0) (fun j => P 0 j.succ)))) := by
          rw [frontPrepended_eq_relabel_finPrepended]
          exact (hasQaryRankOneOrientedPairing_relabelBlockCode_iff
            c ((finSuccEquiv 0).trans finSuccEquivLast.symm)
              (finPrependedScalarRowSpaceAsBlock (K := K)
                (readSuccessor
                  (extendedRows c P' H' Q' A' D
                    (H 0) (Q 0) (fun j => P 0 j.succ))))).mpr hlast
        rw [← hdict,
          frontPrepended_readSuccessor_eq_relabel_flattenRows_exact] at hfront
        exact (hasQaryRankOneOrientedPairing_relabelBlockCode_fin_iff
          c ((frontRankBoxEquiv 0 0).trans finSumFinEquiv)
            (scalarRowSpaceAsBlock
              (flattenRows (rankBoxedRows c P H Q A D)))).mp hfront

/-- Exact universal theorem obtained by combining the rank-box normal form
with the exhaustive recursive pairing theorem. -/
theorem every_qary_selfDualCode_has_rankOne_orientedPairing_exact
    {n : ℕ} (hn : 0 < n) (c : K) (hc : c ^ 2 = (-1 : K))
    (h2 : (2 : K) ≠ 0)
    {C : Submodule K (QaryBlockRow K (Fin n))}
    (hC : QaryBlockSelfDualCode C) :
    HasQaryRankOneOrientedPairing c C := by
  obtain ⟨k, r, _, hkr, σ, b, ell, D, hD, hoff, hnormal⟩ :=
    every_qary_selfDualCode_has_rankBoxed_normalForm c hc h2 hC
  let P := paperPivotCoefficients c b ell
  let H := terminalFirst ell
  let Q := terminalDefect c ell
  let A := forcedMasterCoefficients Q D
  have hpm : PivotMasterRelations Q A D := by
    intro s i
    simp [A, forcedMasterCoefficients]
  have hpp : PivotGramRelations c P H Q := by
    exact paperPivotGramRelations c b ell
      (by simpa [pow_two] using hc) h2 hoff
  have hboxed : HasQaryRankOneOrientedPairing c
      (scalarRowSpaceAsBlock
        (flattenRows (paperRankBoxedRows c b ell D))) := by
    simpa [paperRankBoxedRows, determinedRankBoxedRows, P, H, Q, A] using
      rankBoxed_flatten_has_rankOne_orientedPairing_exact
        (K := K) (k := k) (r := r) (by omega) c P H Q A D
          hc h2 hD hpm hpp
  have hcode :
      scalarRowSpaceAsBlock
          (flattenRows (paperRankBoxedRows c b ell D)) =
        relabelBlockCode (K := K) (finSumFinEquiv.symm.trans σ) C := by
    rw [scalarRowSpaceAsBlock_flattenRows_exact, ← hnormal,
      relabelBlockCode_trans_exact]
  rw [hcode] at hboxed
  exact (hasQaryRankOneOrientedPairing_relabelBlockCode_fin_iff
    c (finSumFinEquiv.symm.trans σ) C).mp hboxed

end BuildingUpFormalization.Components.QaryRankOneUniversalPairing
