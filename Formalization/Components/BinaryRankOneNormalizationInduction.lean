import Formalization.Components.BinaryRankOneNormalization

set_option autoImplicit false
namespace BuildingUpFormalization.Components.BinaryRankOneNormalization

open BuildingUpFormalization.Components.Foundations
open BuildingUpFormalization.Components.PermutationEquivalence
open BuildingUpFormalization.Components.RankBoxed
open BuildingUpFormalization.Components.SplitBoxed

@[simp] theorem binaryHead2_zero (a b : ZMod 2) : head2 a b 0 = a := rfl
@[simp] theorem binaryHead2_one (a b : ZMod 2) : head2 a b 1 = b := rfl

def prependRankOneBlock {k : ℕ}
    (h : SplitBlock (ZMod 2)) (T : RankBoxRow (ZMod 2) k 1) :
    RankBoxRow (ZMod 2) (k + 1) 1
  | .inl j => Fin.cases h (fun i => T (.inl i)) j
  | .inr t => T (.inr t)

def binaryBlockExtensionRows {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1) :
    RankBoxIndex (k + 1) 1 → RankBoxRow (ZMod 2) (k + 1) 1
  | .inl j => Fin.cases
      (prependRankOneBlock (head2 1 0) Z)
      (fun i =>
        let y := rankBoxRowInner Z (R (.inl i))
        prependRankOneBlock (head2 y y) (R (.inl i))) j
  | .inr t =>
      let y := rankBoxRowInner Z (R (.inr t))
      prependRankOneBlock (head2 y y) (R (.inr t))

def blockSwap (B : SplitBlock (ZMod 2)) : SplitBlock (ZMod 2) :=
  head2 (B 1) (B 0)

@[simp] theorem blockSwap_head2_same (a : ZMod 2) :
    blockSwap (head2 a a) = head2 a a := by
  funext q
  fin_cases q <;> rfl

def orientNewHead {k : ℕ} (s : ZMod 2)
    (T : RankBoxRow (ZMod 2) (k + 1) 1) :
    RankBoxRow (ZMod 2) (k + 1) 1
  | .inl j => Fin.cases (if s = 0 then blockSwap (T (.inl 0)) else T (.inl 0))
      (fun i => T (.inl (Fin.succ i))) j
  | .inr t => T (.inr t)

theorem orient_head2_one_add {s : ZMod 2} :
    (if s = 0 then blockSwap (head2 (1 + s) s) else head2 (1 + s) s) =
      head2 0 1 := by
  fin_cases s
  · change blockSwap (head2 (1 + 0) 0) = head2 0 1
    funext q
    fin_cases q <;> rfl
  · change head2 (1 + 1) 1 = head2 0 1
    have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    rw [htwo]

def extensionPivotDefect {k : ℕ} (Z : RankBoxRow (ZMod 2) k 1)
    (i : Fin k) : ZMod 2 := blockDefectLinear 1 (Z (.inl i))

def extensionCorrectedTop {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1) :
    RankBoxRow (ZMod 2) (k + 1) 1 :=
  let E := binaryBlockExtensionRows Z R
  let U := E (.inl 0) +
    ∑ i : Fin k, extensionPivotDefect Z i • E (.inl (Fin.succ i))
  U + (U (.inr 0) 1) • E (.inr 0)

def binaryUnorientedCorrectedExtensionRows {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1) :
    RankBoxIndex (k + 1) 1 → RankBoxRow (ZMod 2) (k + 1) 1
  | .inl j => Fin.cases (extensionCorrectedTop Z R)
      (fun i => binaryBlockExtensionRows Z R (.inl (Fin.succ i))) j
  | .inr t => binaryBlockExtensionRows Z R (.inr t)

def binaryCorrectedExtensionRows {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1) :
    RankBoxIndex (k + 1) 1 → RankBoxRow (ZMod 2) (k + 1) 1 :=
  let E := binaryBlockExtensionRows Z R
  let T := extensionCorrectedTop Z R
  let S : RankBoxIndex (k + 1) 1 → RankBoxRow (ZMod 2) (k + 1) 1
    | .inl j => Fin.cases T (fun i => E (.inl (Fin.succ i))) j
    | .inr t => E (.inr t)
  orientNewHead (T (.inl 0) 1) ∘ S

theorem blockDefect_binaryCz_pivot {k : ℕ}
    (b : Fin k → Fin k → ZMod 2) (i j : Fin k) :
    blockDefectLinear 1 (binaryCzRankOneRows b (.inl i) (.inl j)) =
      if i = j then 1 else 0 := by
  simp [binaryCzRankOneRows, rankBoxedRows]

theorem blockDefect_binaryCz_terminal {k : ℕ}
    (b : Fin k → Fin k → ZMod 2) (i : Fin k) :
    blockDefectLinear 1 (binaryCzRankOneRows b (.inl i) (.inr 0)) = 1 := by
  simp [binaryCzRankOneRows, rankBoxedRows]

theorem blockDefect_binaryCz_master {k : ℕ}
    (b : Fin k → Fin k → ZMod 2) (x : RankBoxIndex k 1) :
    blockDefectLinear 1 (binaryCzRankOneRows b (.inr 0) x) = 0 := by
  cases x <;> simp [binaryCzRankOneRows, rankBoxedRows]

theorem extensionCorrectedTop_oldPivot_defect {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (b : Fin k → Fin k → ZMod 2) (j : Fin k) :
    blockDefectLinear 1
      (extensionCorrectedTop Z (binaryCzRankOneRows b) (.inl (Fin.succ j))) = 0 := by
  classical
  simp [extensionCorrectedTop, binaryBlockExtensionRows, prependRankOneBlock,
    extensionPivotDefect, blockDefect_binaryCz_pivot,
    blockDefect_binaryCz_master]
  exact CharTwo.add_self_eq_zero _

theorem sum_blockDefect_eq_rankBoxRowInner_self {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1) :
    (∑ i : Fin k, blockDefectLinear 1 (Z (.inl i))) +
      ∑ t : Fin 1, blockDefectLinear 1 (Z (.inr t)) =
        rankBoxRowInner Z Z := by
  have hsq (a : ZMod 2) : a * a = a := by
    fin_cases a <;> rfl
  unfold rankBoxRowInner
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp [blockDefectLinear, blockDefect, splitBlockInner, dot, hsq,
      sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  · apply Finset.sum_congr rfl
    intro t _
    simp [blockDefectLinear, blockDefect, splitBlockInner, dot, hsq,
      sub_eq_add_neg, CharTwo.neg_eq, add_comm]

theorem extensionCorrectedTop_terminal {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (b : Fin k → Fin k → ZMod 2)
    (hZ : rankBoxRowInner Z Z = 1) :
    extensionCorrectedTop Z (binaryCzRankOneRows b) (.inr 0) = head2 1 0 := by
  classical
  have hsum := sum_blockDefect_eq_rankBoxRowInner_self Z
  rw [hZ] at hsum
  have hUdef : blockDefectLinear 1
      ((binaryBlockExtensionRows Z (binaryCzRankOneRows b) (.inl 0) +
        ∑ i : Fin k, extensionPivotDefect Z i •
          binaryBlockExtensionRows Z (binaryCzRankOneRows b)
            (.inl (Fin.succ i))) (.inr 0)) = 1 := by
    simpa [binaryBlockExtensionRows, prependRankOneBlock,
      extensionPivotDefect, blockDefect_binaryCz_terminal, add_comm] using hsum
  let U := binaryBlockExtensionRows Z (binaryCzRankOneRows b) (.inl 0) +
    ∑ i : Fin k, extensionPivotDefect Z i •
      binaryBlockExtensionRows Z (binaryCzRankOneRows b) (.inl (Fin.succ i))
  have hU : blockDefectLinear 1 (U (.inr 0)) = 1 := by exact hUdef
  funext q
  fin_cases q
  · change U (.inr 0) 0 + U (.inr 0) 1 * 1 = 1
    simpa [blockDefectLinear, blockDefect, sub_eq_add_neg, CharTwo.neg_eq,
      add_comm] using hU
  · change U (.inr 0) 1 + U (.inr 0) 1 * 1 = 0
    simpa using CharTwo.add_self_eq_zero (U (.inr 0) 1)

theorem rankBoxRowInner_binaryCz_master {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (b : Fin k → Fin k → ZMod 2)
    (hZ : rankBoxRowInner Z Z = 1) :
    rankBoxRowInner Z (binaryCzRankOneRows b (.inr 0)) = 1 := by
  have hsum := sum_blockDefect_eq_rankBoxRowInner_self Z
  rw [hZ] at hsum
  simpa [rankBoxRowInner, binaryCzRankOneRows, rankBoxedRows,
    isotropicLineBlock, splitBlockInner, dot, head2,
    blockDefectLinear, blockDefect, sub_eq_add_neg, CharTwo.neg_eq,
    add_comm] using hsum

theorem extensionCorrectedTop_newHead {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1) :
    let T := extensionCorrectedTop Z R
    T (.inl 0) = head2 (1 + T (.inl 0) 1) (T (.inl 0) 1) := by
  classical
  dsimp
  funext q
  fin_cases q
  · simp [extensionCorrectedTop, binaryBlockExtensionRows,
      prependRankOneBlock, head2]
    abel
  · rfl

theorem splitBlock_eq_identical_of_defect_zero
    (B : SplitBlock (ZMod 2)) (hB : blockDefectLinear 1 B = 0) :
    B = head2 (B 0) (B 0) := by
  have heq : B 1 = B 0 := by
    simpa [blockDefectLinear, blockDefect] using sub_eq_zero.mp hB
  funext q
  fin_cases q
  · rfl
  · exact heq

def binaryCorrectedExtensionB {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1) :
    Fin (k + 1) → Fin (k + 1) → ZMod 2 :=
  fun i j => binaryCorrectedExtensionRows Z R (.inl i) (.inl j) 0

theorem binaryCorrectedExtensionRows_diagonal {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (b : Fin k → Fin k → ZMod 2)
    (hdiag : ∀ i, b i i = 0) (i : Fin (k + 1)) :
    binaryCorrectedExtensionRows Z (binaryCzRankOneRows b) (.inl i) (.inl i) =
      head2 0 1 := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · let T := extensionCorrectedTop Z (binaryCzRankOneRows b)
    let s := T (.inl 0) 1
    have hhead : T (.inl 0) = head2 (1 + s) s := by
      simpa [T, s] using
        extensionCorrectedTop_newHead Z (binaryCzRankOneRows b)
    change orientNewHead s T (.inl 0) = head2 0 1
    change (if s = 0 then blockSwap (T (.inl 0)) else T (.inl 0)) =
      head2 0 1
    rw [hhead]
    change (if s = 0 then blockSwap (head2 (1 + s) s)
      else head2 (1 + s) s) = head2 0 1
    exact orient_head2_one_add
  · simp [binaryCorrectedExtensionRows, orientNewHead,
      binaryBlockExtensionRows, prependRankOneBlock,
      binaryCzRankOneRows_pivot_diagonal b j (hdiag j)]
    simp [splitDiagonalBlock, head2]

theorem binaryCorrectedExtensionRows_terminal {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (b : Fin k → Fin k → ZMod 2)
    (hZ : rankBoxRowInner Z Z = 1) (i : Fin (k + 1)) :
    binaryCorrectedExtensionRows Z (binaryCzRankOneRows b) (.inl i) (.inr 0) =
      head2 1 0 := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [binaryCorrectedExtensionRows, orientNewHead]
    exact extensionCorrectedTop_terminal Z b hZ
  · simp [binaryCorrectedExtensionRows, orientNewHead,
      binaryBlockExtensionRows, prependRankOneBlock,
      binaryCzRankOneRows_pivot_terminal]

theorem binaryCorrectedExtensionRows_master {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (b : Fin k → Fin k → ZMod 2)
    (hZ : rankBoxRowInner Z Z = 1) (x : RankBoxIndex (k + 1) 1) :
    binaryCorrectedExtensionRows Z (binaryCzRankOneRows b) (.inr 0) x =
      head2 1 1 := by
  cases x with
  | inl i =>
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · have hy := rankBoxRowInner_binaryCz_master Z b hZ
        simp [binaryCorrectedExtensionRows, orientNewHead,
          binaryBlockExtensionRows, prependRankOneBlock, hy, blockSwap]
      · simp [binaryCorrectedExtensionRows, orientNewHead,
          binaryBlockExtensionRows, prependRankOneBlock,
          binaryCzRankOneRows_master_pivot]
  | inr t =>
      have ht : t = 0 := Subsingleton.elim _ _
      subst t
      simp [binaryCorrectedExtensionRows, orientNewHead,
        binaryBlockExtensionRows, prependRankOneBlock,
        binaryCzRankOneRows_master_terminal]

theorem binaryCorrectedExtensionRows_offDiagonal {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (b : Fin k → Fin k → ZMod 2)
    {i j : Fin (k + 1)} (hij : i ≠ j) :
    binaryCorrectedExtensionRows Z (binaryCzRankOneRows b) (.inl i) (.inl j) =
      head2 (binaryCorrectedExtensionB Z (binaryCzRankOneRows b) i j)
        (binaryCorrectedExtensionB Z (binaryCzRankOneRows b) i j) := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact (hij rfl).elim
    · have hdef := extensionCorrectedTop_oldPivot_defect Z b j
      have heq := splitBlock_eq_identical_of_defect_zero
        (extensionCorrectedTop Z (binaryCzRankOneRows b) (.inl (Fin.succ j))) hdef
      simpa [binaryCorrectedExtensionRows, orientNewHead,
        binaryCorrectedExtensionB] using heq
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · simp [binaryCorrectedExtensionRows, orientNewHead,
        binaryCorrectedExtensionRows, binaryCorrectedExtensionB,
        binaryBlockExtensionRows, prependRankOneBlock, blockSwap]
    · have hij' : i ≠ j := by
        intro h
        subst j
        exact hij rfl
      simp [binaryCorrectedExtensionRows, orientNewHead,
        binaryCorrectedExtensionB, binaryBlockExtensionRows,
        prependRankOneBlock,
        binaryCzRankOneRows_pivot_offDiagonal b hij',
        isotropicLineBlock, head2]

theorem binaryCorrectedExtensionB_diagonal {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (b : Fin k → Fin k → ZMod 2)
    (hdiag : ∀ i, b i i = 0) (i : Fin (k + 1)) :
    binaryCorrectedExtensionB Z (binaryCzRankOneRows b) i i = 0 := by
  have h := congrFun (binaryCorrectedExtensionRows_diagonal Z b hdiag i) 0
  simpa [binaryCorrectedExtensionB] using h

theorem binaryCorrectedExtensionRows_eq_binaryCz {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (b : Fin k → Fin k → ZMod 2)
    (hdiag : ∀ i, b i i = 0)
    (hZ : rankBoxRowInner Z Z = 1) :
    binaryCorrectedExtensionRows Z (binaryCzRankOneRows b) =
      binaryCzRankOneRows
        (binaryCorrectedExtensionB Z (binaryCzRankOneRows b)) := by
  funext r x
  cases r with
  | inl i =>
      cases x with
      | inl j =>
          by_cases hij : i = j
          · subst j
            rw [binaryCorrectedExtensionRows_diagonal Z b hdiag i]
            symm
            exact binaryCzRankOneRows_pivot_diagonal _ i
              (binaryCorrectedExtensionB_diagonal Z b hdiag i)
          · rw [binaryCorrectedExtensionRows_offDiagonal Z b hij,
              binaryCzRankOneRows_pivot_offDiagonal _ hij]
            simp [isotropicLineBlock, head2]
      | inr t =>
          have ht : t = 0 := Subsingleton.elim _ _
          subst t
          rw [binaryCorrectedExtensionRows_terminal Z b hZ i,
            binaryCzRankOneRows_pivot_terminal]
  | inr s =>
      have hs : s = 0 := Subsingleton.elim _ _
      subst s
      rw [binaryCorrectedExtensionRows_master Z b hZ x]
      cases x with
      | inl j => rw [binaryCzRankOneRows_master_pivot]
      | inr t => rw [binaryCzRankOneRows_master_terminal]

theorem rankBoxRowInner_prependRankOneBlock {k : ℕ}
    (h g : SplitBlock (ZMod 2)) (R S : RankBoxRow (ZMod 2) k 1) :
    rankBoxRowInner (prependRankOneBlock h R)
        (prependRankOneBlock g S) =
      splitBlockInner h g + rankBoxRowInner R S := by
  simp only [rankBoxRowInner, prependRankOneBlock]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [splitBlockInner, head2]
  ring

@[simp] theorem dot_head2_same_same (a b : ZMod 2) :
    dot (head2 a a) (head2 b b) = 0 := by
  simp [dot, Fin.sum_univ_two, head2, CharTwo.add_self_eq_zero]

@[simp] theorem dot_head2_one_zero_same (a : ZMod 2) :
    dot (head2 1 0) (head2 a a) = a := by
  simp [dot, Fin.sum_univ_two, head2]

@[simp] theorem dot_head2_same_one_zero (a : ZMod 2) :
    dot (head2 a a) (head2 1 0) = a := by
  simp [dot, Fin.sum_univ_two, head2]

theorem binaryBlockExtensionRows_pairwiseOrthogonal {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1)
    (hZ : rankBoxRowInner Z Z = 1)
    (hR : RankBoxedPairwiseOrthogonal R) :
    RankBoxedPairwiseOrthogonal (binaryBlockExtensionRows Z R) := by
  intro i j
  cases i with
  | inl i =>
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · cases j with
        | inl j =>
            rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
            · rw [show binaryBlockExtensionRows Z R (.inl 0) =
                    prependRankOneBlock (head2 1 0) Z by rfl,
                  rankBoxRowInner_prependRankOneBlock, hZ]
              exact CharTwo.add_self_eq_zero 1
            · rw [show binaryBlockExtensionRows Z R (.inl 0) =
                    prependRankOneBlock (head2 1 0) Z by rfl,
                  show binaryBlockExtensionRows Z R (.inl (Fin.succ j)) =
                    prependRankOneBlock
                      (head2 (rankBoxRowInner Z (R (.inl j)))
                        (rankBoxRowInner Z (R (.inl j)))) (R (.inl j)) by rfl,
                  rankBoxRowInner_prependRankOneBlock]
              simp [splitBlockInner, head2, CharTwo.add_self_eq_zero]
        | inr t =>
            rw [show binaryBlockExtensionRows Z R (.inl 0) =
                    prependRankOneBlock (head2 1 0) Z by rfl,
                show binaryBlockExtensionRows Z R (.inr t) =
                    prependRankOneBlock
                      (head2 (rankBoxRowInner Z (R (.inr t)))
                        (rankBoxRowInner Z (R (.inr t)))) (R (.inr t)) by rfl,
                rankBoxRowInner_prependRankOneBlock]
            simp [splitBlockInner, head2, CharTwo.add_self_eq_zero]
      · cases j with
        | inl j =>
            rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
            · rw [show binaryBlockExtensionRows Z R (.inl (Fin.succ i)) =
                    prependRankOneBlock
                      (head2 (rankBoxRowInner Z (R (.inl i)))
                        (rankBoxRowInner Z (R (.inl i)))) (R (.inl i)) by rfl,
                  show binaryBlockExtensionRows Z R (.inl 0) =
                    prependRankOneBlock (head2 1 0) Z by rfl,
                  rankBoxRowInner_prependRankOneBlock]
              rw [rankBoxRowInner_comm]
              simp [splitBlockInner, head2, CharTwo.add_self_eq_zero]
            · rw [show binaryBlockExtensionRows Z R (.inl (Fin.succ i)) =
                    prependRankOneBlock
                      (head2 (rankBoxRowInner Z (R (.inl i)))
                        (rankBoxRowInner Z (R (.inl i)))) (R (.inl i)) by rfl,
                  show binaryBlockExtensionRows Z R (.inl (Fin.succ j)) =
                    prependRankOneBlock
                      (head2 (rankBoxRowInner Z (R (.inl j)))
                        (rankBoxRowInner Z (R (.inl j)))) (R (.inl j)) by rfl,
                  rankBoxRowInner_prependRankOneBlock, hR (.inl i) (.inl j)]
              simp [splitBlockInner, head2, CharTwo.add_self_eq_zero]
        | inr t =>
            rw [show binaryBlockExtensionRows Z R (.inl (Fin.succ i)) =
                    prependRankOneBlock
                      (head2 (rankBoxRowInner Z (R (.inl i)))
                        (rankBoxRowInner Z (R (.inl i)))) (R (.inl i)) by rfl,
                show binaryBlockExtensionRows Z R (.inr t) =
                    prependRankOneBlock
                      (head2 (rankBoxRowInner Z (R (.inr t)))
                        (rankBoxRowInner Z (R (.inr t)))) (R (.inr t)) by rfl,
                rankBoxRowInner_prependRankOneBlock, hR (.inl i) (.inr t)]
            simp [splitBlockInner, head2, CharTwo.add_self_eq_zero]
  | inr s =>
      cases j with
      | inl j =>
          rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · rw [show binaryBlockExtensionRows Z R (.inr s) =
                  prependRankOneBlock
                    (head2 (rankBoxRowInner Z (R (.inr s)))
                      (rankBoxRowInner Z (R (.inr s)))) (R (.inr s)) by rfl,
                show binaryBlockExtensionRows Z R (.inl 0) =
                  prependRankOneBlock (head2 1 0) Z by rfl,
                rankBoxRowInner_prependRankOneBlock]
            rw [rankBoxRowInner_comm]
            simp [splitBlockInner, head2, CharTwo.add_self_eq_zero]
          · rw [show binaryBlockExtensionRows Z R (.inr s) =
                  prependRankOneBlock
                    (head2 (rankBoxRowInner Z (R (.inr s)))
                      (rankBoxRowInner Z (R (.inr s)))) (R (.inr s)) by rfl,
                show binaryBlockExtensionRows Z R (.inl (Fin.succ j)) =
                  prependRankOneBlock
                    (head2 (rankBoxRowInner Z (R (.inl j)))
                      (rankBoxRowInner Z (R (.inl j)))) (R (.inl j)) by rfl,
                rankBoxRowInner_prependRankOneBlock, hR (.inr s) (.inl j)]
            simp [splitBlockInner, head2, CharTwo.add_self_eq_zero]
      | inr t =>
          rw [show binaryBlockExtensionRows Z R (.inr s) =
                  prependRankOneBlock
                    (head2 (rankBoxRowInner Z (R (.inr s)))
                      (rankBoxRowInner Z (R (.inr s)))) (R (.inr s)) by rfl,
              show binaryBlockExtensionRows Z R (.inr t) =
                  prependRankOneBlock
                    (head2 (rankBoxRowInner Z (R (.inr t)))
                      (rankBoxRowInner Z (R (.inr t)))) (R (.inr t)) by rfl,
              rankBoxRowInner_prependRankOneBlock, hR (.inr s) (.inr t)]
          simp [splitBlockInner, head2, CharTwo.add_self_eq_zero]

theorem extensionCorrectedTop_mem_rankBoxedRowSpace {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1) :
    extensionCorrectedTop Z R ∈
      rankBoxedRowSpace (binaryBlockExtensionRows Z R) := by
  let E := binaryBlockExtensionRows Z R
  have hrow (i : RankBoxIndex (k + 1) 1) :
      E i ∈ rankBoxedRowSpace E :=
    Submodule.subset_span (Set.mem_range_self i)
  have hsum : (∑ i : Fin k,
      extensionPivotDefect Z i • E (.inl (Fin.succ i))) ∈
      rankBoxedRowSpace E := by
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (hrow (.inl (Fin.succ i))))
  have hU : E (.inl 0) + (∑ i : Fin k,
      extensionPivotDefect Z i • E (.inl (Fin.succ i))) ∈
      rankBoxedRowSpace E := Submodule.add_mem _ (hrow (.inl 0)) hsum
  exact Submodule.add_mem _ hU
    (Submodule.smul_mem _ _ (hrow (.inr 0)))

theorem binaryUnorientedCorrectedExtensionRows_mem {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1)
    (i : RankBoxIndex (k + 1) 1) :
    binaryUnorientedCorrectedExtensionRows Z R i ∈
      rankBoxedRowSpace (binaryBlockExtensionRows Z R) := by
  cases i with
  | inl i =>
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · exact extensionCorrectedTop_mem_rankBoxedRowSpace Z R
      · exact Submodule.subset_span
          (Set.mem_range_self (Sum.inl (Fin.succ i) : RankBoxIndex (k + 1) 1))
  | inr t =>
      exact Submodule.subset_span
        (Set.mem_range_self (Sum.inr t : RankBoxIndex (k + 1) 1))

theorem binaryUnorientedCorrectedExtensionRows_pairwiseOrthogonal {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1)
    (hZ : rankBoxRowInner Z Z = 1)
    (hR : RankBoxedPairwiseOrthogonal R) :
    RankBoxedPairwiseOrthogonal
      (binaryUnorientedCorrectedExtensionRows Z R) := by
  have hraw := binaryBlockExtensionRows_pairwiseOrthogonal Z R hZ hR
  have hle := rankBoxedRowSpace_le_orthogonal hraw
  intro i j
  have hi := binaryUnorientedCorrectedExtensionRows_mem Z R i
  have hj := binaryUnorientedCorrectedExtensionRows_mem Z R j
  have hjorth := hle hj
  have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hjorth) _ hi
  simpa [LinearMap.BilinForm.isOrtho_def, rankBoxRowBilin_apply] using h

@[simp] theorem splitBlockInner_blockSwap (A B : SplitBlock (ZMod 2)) :
    splitBlockInner (blockSwap A) (blockSwap B) = splitBlockInner A B := by
  simp [splitBlockInner, blockSwap, dot, Fin.sum_univ_two, head2]
  ring

theorem rankBoxRowInner_orientNewHead {k : ℕ} (s : ZMod 2)
    (A B : RankBoxRow (ZMod 2) (k + 1) 1) :
    rankBoxRowInner (orientNewHead s A) (orientNewHead s B) =
      rankBoxRowInner A B := by
  by_cases hs : s = 0
  · simp only [rankBoxRowInner]
    simp_rw [Fin.sum_univ_succ]
    simp [orientNewHead, hs]
  · simp only [rankBoxRowInner]
    simp_rw [Fin.sum_univ_succ]
    simp [orientNewHead, hs]

theorem binaryCorrectedExtensionRows_eq_orient {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1) :
    binaryCorrectedExtensionRows Z R = fun i =>
      orientNewHead (extensionCorrectedTop Z R (.inl 0) 1)
        (binaryUnorientedCorrectedExtensionRows Z R i) := by
  funext i x q
  cases i with
  | inl i =>
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
        rfl
  | inr t => rfl

theorem binaryCorrectedExtensionRows_pairwiseOrthogonal {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1)
    (hZ : rankBoxRowInner Z Z = 1)
    (hR : RankBoxedPairwiseOrthogonal R) :
    RankBoxedPairwiseOrthogonal (binaryCorrectedExtensionRows Z R) := by
  rw [binaryCorrectedExtensionRows_eq_orient]
  intro i j
  rw [rankBoxRowInner_orientNewHead]
  exact binaryUnorientedCorrectedExtensionRows_pairwiseOrthogonal Z R hZ hR i j

theorem binaryCzRankOneRows_pivot_inner_formula {k : ℕ}
    (b : Fin k → Fin k → ZMod 2)
    (hdiag : ∀ i, b i i = 0) {i j : Fin k} (hij : i ≠ j) :
    rankBoxRowInner (binaryCzRankOneRows b (.inl i))
      (binaryCzRankOneRows b (.inl j)) = b i j + b j i + 1 := by
  have htwo : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
  unfold rankBoxRowInner
  simp only [binaryCzRankOneRows, rankBoxedRows]
  have hterm : ∀ x : Fin k,
      splitBlockInner (splitAffineBlock 1 (b i x) (if i = x then 1 else 0))
        (splitAffineBlock 1 (b j x) (if j = x then 1 else 0)) =
      if x = i then b j i else if x = j then b i j else 0 := by
    intro x
    by_cases hxi : x = i
    · subst x
      simp [hdiag, hij, Ne.symm hij, splitAffineBlock,
        splitBlockInner, dot, head2, htwo]
    · by_cases hxj : x = j
      · subst x
        simp [hdiag, hij, Ne.symm hij, splitAffineBlock,
          splitBlockInner, dot, head2, htwo]
      · simp [hxi, hxj, Ne.symm hxi, Ne.symm hxj, splitAffineBlock,
          splitBlockInner, dot, head2]
        exact CharTwo.add_self_eq_zero _
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  have hsplit : ∀ x : Fin k,
      (if x = i then b j i else if x = j then b i j else 0) =
        (if x = i then b j i else 0) + (if x = j then b i j else 0) := by
    intro x
    by_cases hxi : x = i <;> by_cases hxj : x = j <;>
      simp [hxi, hxj, hij, Ne.symm hij]
  rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_add_distrib]
  simp [splitAffineBlock, splitBlockInner, dot, head2]
  abel

theorem binaryCorrectedExtensionB_opposite {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (b : Fin k → Fin k → ZMod 2)
    (hdiag : ∀ i, b i i = 0)
    (hopposite : ∀ i j, i ≠ j → b i j + b j i = 1)
    (hZ : rankBoxRowInner Z Z = 1) :
    ∀ i j, i ≠ j →
      binaryCorrectedExtensionB Z (binaryCzRankOneRows b) i j +
        binaryCorrectedExtensionB Z (binaryCzRankOneRows b) j i = 1 := by
  let b' := binaryCorrectedExtensionB Z (binaryCzRankOneRows b)
  have hR : RankBoxedPairwiseOrthogonal (binaryCzRankOneRows b) :=
    binaryCzRankOneRows_pairwiseOrthogonal b hdiag hopposite
  have hcorr := binaryCorrectedExtensionRows_pairwiseOrthogonal Z _ hZ hR
  have heq := binaryCorrectedExtensionRows_eq_binaryCz Z b hdiag hZ
  intro i j hij
  have hzero := hcorr (.inl i) (.inl j)
  rw [heq] at hzero
  rw [binaryCzRankOneRows_pivot_inner_formula b'
    (binaryCorrectedExtensionB_diagonal Z b hdiag) hij] at hzero
  have hneg : b' i j + b' j i = -(1 : ZMod 2) :=
    eq_neg_of_add_eq_zero_left hzero
  simpa [b', CharTwo.neg_eq] using hneg

theorem binaryUnorientedCorrectedExtensionRows_rowSpace_eq {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1) :
    rankBoxedRowSpace (binaryUnorientedCorrectedExtensionRows Z R) =
      rankBoxedRowSpace (binaryBlockExtensionRows Z R) := by
  let E := binaryBlockExtensionRows Z R
  let S : RankBoxRow (ZMod 2) (k + 1) 1 :=
    ∑ i : Fin k, extensionPivotDefect Z i • E (.inl (Fin.succ i))
  let U := E (.inl 0) + S
  let c := U (.inr 0) 1
  apply le_antisymm
  · rw [rankBoxedRowSpace]
    exact Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact binaryUnorientedCorrectedExtensionRows_mem Z R i)
  · rw [rankBoxedRowSpace]
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl i =>
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · have htop : extensionCorrectedTop Z R ∈
              rankBoxedRowSpace (binaryUnorientedCorrectedExtensionRows Z R) :=
            Submodule.subset_span (Set.mem_range_self
              (Sum.inl 0 : RankBoxIndex (k + 1) 1))
          have hmaster : E (.inr 0) ∈
              rankBoxedRowSpace (binaryUnorientedCorrectedExtensionRows Z R) := by
            exact Submodule.subset_span (Set.mem_range_self
              (Sum.inr 0 : RankBoxIndex (k + 1) 1))
          have hS : S ∈
              rankBoxedRowSpace (binaryUnorientedCorrectedExtensionRows Z R) := by
            exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
              (Submodule.subset_span
                (Set.mem_range_self
                  (Sum.inl (Fin.succ j) : RankBoxIndex (k + 1) 1))))
          have hcalc := Submodule.sub_mem _
            (Submodule.sub_mem _ htop (Submodule.smul_mem _ c hmaster)) hS
          simpa [extensionCorrectedTop, E, S, U, c] using hcalc
        · exact Submodule.subset_span
            (Set.mem_range_self
              (Sum.inl (Fin.succ i) : RankBoxIndex (k + 1) 1))
    | inr t =>
        exact Submodule.subset_span (Set.mem_range_self
          (Sum.inr t : RankBoxIndex (k + 1) 1))

theorem rowSpace_flattenRankBoxedRows {k r : ℕ}
    (R : RankBoxIndex k r → RankBoxRow (ZMod 2) k r) :
    rowSpace (flattenRankBoxedRows R) =
      (rankBoxedRowSpace R).map
        (flattenRankBoxLinearEquiv (K := ZMod 2) (k := k) (r := r)).toLinearMap := by
  unfold rowSpace rankBoxedRowSpace
  rw [Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨R (finSumFinEquiv.symm i),
      ⟨finSumFinEquiv.symm i, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
    exact ⟨finSumFinEquiv j, by
      simp [flattenRankBoxedRows, flattenRankBoxLinearEquiv_apply]⟩

def orientNewHeadPerm (k : ℕ) (s : ZMod 2) :
    Equiv.Perm (Fin (2 * ((k + 1) + 1))) :=
  if s = 0 then
    (rankBoxCoordEquivFin (k + 1) 1).symm.trans
      ((Equiv.swap
        ((Sum.inl (0 : Fin (k + 1)) : RankBoxIndex (k + 1) 1), (0 : Fin 2))
        ((Sum.inl (0 : Fin (k + 1)) : RankBoxIndex (k + 1) 1), (1 : Fin 2))).trans
        (rankBoxCoordEquivFin (k + 1) 1))
  else Equiv.refl _

theorem flattenRankBoxRow_orientNewHead {k : ℕ} (s : ZMod 2)
    (A : RankBoxRow (ZMod 2) (k + 1) 1) :
    flattenRankBoxRow (orientNewHead s A) =
      permuteVec (orientNewHeadPerm k s) (flattenRankBoxRow A) := by
  funext j
  let p := (rankBoxCoordEquivFin (k + 1) 1).symm j
  have hj : j = rankBoxCoordEquivFin (k + 1) 1 p := by
    simp [p]
  rw [hj]
  rcases p with ⟨x, q⟩
  cases x with
  | inl i =>
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · fin_cases q <;> by_cases hs : s = 0 <;>
          simp [flattenRankBoxRow, orientNewHeadPerm, orientNewHead, hs,
            blockSwap, head2, permuteVec]
      · fin_cases q <;> by_cases hs : s = 0 <;>
          simp [flattenRankBoxRow, orientNewHeadPerm, orientNewHead, hs,
            permuteVec, Equiv.swap_apply_of_ne_of_ne]
  | inr t =>
      fin_cases t
      fin_cases q <;> by_cases hs : s = 0 <;>
        simp [flattenRankBoxRow, orientNewHeadPerm, orientNewHead, hs,
          permuteVec, Equiv.swap_apply_of_ne_of_ne]

def castBuildRowsBin {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1) :
    Fin ((k + 1) + 1) → Fin (2 * ((k + 1) + 1)) → ZMod 2 :=
  fun i j => buildRowsBin (flattenRankBoxRow Z) (flattenRankBoxedRows R) i
    (Fin.cast (by omega : 2 * ((k + 1) + 1) = 2 + 2 * (k + 1)) j)

theorem rankBoxCoordEquivFin_val {k r : ℕ}
    (x : RankBoxIndex k r) (q : Fin 2) :
    (rankBoxCoordEquivFin k r (x, q)).val =
      q.val + 2 * (finSumFinEquiv x).val := by
  simp [rankBoxCoordEquivFin, finProdFinEquiv]

def liftRankBoxIndex {k : ℕ} : RankBoxIndex k 1 → RankBoxIndex (k + 1) 1
  | .inl i => .inl (Fin.succ i)
  | .inr t => .inr t

@[simp] theorem finSumFinEquiv_liftRankBoxIndex {k : ℕ} (x : RankBoxIndex k 1) :
    finSumFinEquiv (liftRankBoxIndex x) = Fin.succ (finSumFinEquiv x) := by
  apply Fin.ext
  cases x <;> simp [liftRankBoxIndex, finSumFinEquiv]

theorem cast_new_head_coord {k : ℕ} (q : Fin 2) :
    Fin.cast (by omega : 2 * ((k + 1) + 1) = 2 + 2 * (k + 1))
        (rankBoxCoordEquivFin (k + 1) 1
          ((Sum.inl 0 : RankBoxIndex (k + 1) 1), q)) =
      Fin.castAdd (2 * (k + 1)) q := by
  apply Fin.ext
  simpa using rankBoxCoordEquivFin_val
    (k := k + 1) (r := 1) (Sum.inl 0) q

theorem cast_liftRankBox_coord {k : ℕ} (x : RankBoxIndex k 1) (q : Fin 2) :
    Fin.cast (by omega : 2 * ((k + 1) + 1) = 2 + 2 * (k + 1))
        (rankBoxCoordEquivFin (k + 1) 1 (liftRankBoxIndex x, q)) =
      Fin.natAdd 2 (rankBoxCoordEquivFin k 1 (x, q)) := by
  apply Fin.ext
  change (rankBoxCoordEquivFin (k + 1) 1 (liftRankBoxIndex x, q)).val =
    2 + (rankBoxCoordEquivFin k 1 (x, q)).val
  rw [rankBoxCoordEquivFin_val, rankBoxCoordEquivFin_val]
  cases x <;> simp [liftRankBoxIndex, finSumFinEquiv] <;> omega

theorem rankBoxIndex_new_or_lift {k : ℕ} (x : RankBoxIndex (k + 1) 1) :
    x = .inl 0 ∨ ∃ old : RankBoxIndex k 1, x = liftRankBoxIndex old := by
  cases x with
  | inl i =>
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨.inl i, rfl⟩
  | inr t => exact Or.inr ⟨.inr t, rfl⟩

@[simp] theorem fin_castAdd_zero (n m : ℕ) :
    Fin.castAdd n (0 : Fin (m + 1)) = 0 := by
  apply Fin.ext
  simp

@[simp] theorem prepend2_castAdd {n : ℕ} (a b : ZMod 2)
    (u : Fin n → ZMod 2) (q : Fin 2) :
    prepend2 a b u (Fin.castAdd n q) = head2 a b q := by
  exact Fin.append_left (head2 a b) u q

@[simp] theorem prepend2_natAdd {n : ℕ} (a b : ZMod 2)
    (u : Fin n → ZMod 2) (j : Fin n) :
    prepend2 a b u (Fin.natAdd 2 j) = u j := by
  exact Fin.append_right (head2 a b) u j

theorem flattenRankBoxedRows_binaryBlockExtensionRows {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1) :
    flattenRankBoxedRows (binaryBlockExtensionRows Z R) =
      castBuildRowsBin Z R := by
  funext i j
  let a := finSumFinEquiv.symm i
  let p := (rankBoxCoordEquivFin (k + 1) 1).symm j
  have hi : i = finSumFinEquiv a := by simp [a]
  have hj : j = rankBoxCoordEquivFin (k + 1) 1 p := by simp [p]
  rw [hi, hj]
  simp only [flattenRankBoxedRows, flattenRankBoxRow, Equiv.symm_apply_apply]
  rcases a with a | t
  · rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a, rfl⟩
    · rcases p with ⟨x, q⟩
      rcases rankBoxIndex_new_or_lift x with rfl | ⟨old, rfl⟩
      ·
        simp only [castBuildRowsBin]
        rw [cast_new_head_coord]
        fin_cases q <;> simp [flattenRankBoxedRows, flattenRankBoxRow,
          castBuildRowsBin, binaryBlockExtensionRows,
          prependRankOneBlock, buildRowsBin, r0,
          liftRankBoxIndex, finSumFinEquiv]
      · simp only [castBuildRowsBin]
        rw [cast_liftRankBox_coord]
        cases old <;> fin_cases q <;> simp [flattenRankBoxedRows, flattenRankBoxRow,
          castBuildRowsBin, binaryBlockExtensionRows,
          prependRankOneBlock, buildRowsBin, r0,
          liftRankBoxIndex, finSumFinEquiv]
    · let oldRow : RankBoxIndex k 1 := .inl a
      have hrow : finSumFinEquiv (.inl (Fin.succ a) : RankBoxIndex (k + 1) 1) =
          Fin.succ (finSumFinEquiv oldRow) := by
        exact finSumFinEquiv_liftRankBoxIndex oldRow
      rw [hrow]
      rcases p with ⟨x, q⟩
      rcases rankBoxIndex_new_or_lift x with rfl | ⟨old, rfl⟩
      ·
        simp only [castBuildRowsBin]
        rw [cast_new_head_coord]
        fin_cases q <;> simp [flattenRankBoxedRows, flattenRankBoxRow,
          castBuildRowsBin, binaryBlockExtensionRows,
          prependRankOneBlock, buildRowsBin, riBin,
          oldRow, dot_flattenRankBoxRow, liftRankBoxIndex, finSumFinEquiv]
      · simp only [castBuildRowsBin]
        rw [cast_liftRankBox_coord]
        cases old <;> fin_cases q <;> simp [flattenRankBoxedRows, flattenRankBoxRow,
          castBuildRowsBin, binaryBlockExtensionRows,
          prependRankOneBlock, buildRowsBin, riBin,
          oldRow, dot_flattenRankBoxRow, liftRankBoxIndex, finSumFinEquiv]
  · have ht : t = 0 := Subsingleton.elim _ _
    subst t
    let oldRow : RankBoxIndex k 1 := .inr 0
    have hrow : finSumFinEquiv (.inr 0 : RankBoxIndex (k + 1) 1) =
        Fin.succ (finSumFinEquiv oldRow) := by
      exact finSumFinEquiv_liftRankBoxIndex oldRow
    rw [hrow]
    rcases p with ⟨x, q⟩
    rcases rankBoxIndex_new_or_lift x with rfl | ⟨old, rfl⟩
    ·
      simp only [castBuildRowsBin]
      rw [cast_new_head_coord]
      fin_cases q <;> simp [flattenRankBoxedRows, flattenRankBoxRow,
        castBuildRowsBin, binaryBlockExtensionRows,
        prependRankOneBlock, buildRowsBin, riBin,
        oldRow, dot_flattenRankBoxRow, liftRankBoxIndex, finSumFinEquiv]
    · simp only [castBuildRowsBin]
      rw [cast_liftRankBox_coord]
      cases old <;> fin_cases q <;> simp [flattenRankBoxedRows, flattenRankBoxRow,
        castBuildRowsBin, binaryBlockExtensionRows,
        prependRankOneBlock, buildRowsBin, riBin,
        oldRow, dot_flattenRankBoxRow, liftRankBoxIndex, finSumFinEquiv]

theorem flatten_corrected_eq_permute_unoriented {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (R : RankBoxIndex k 1 → RankBoxRow (ZMod 2) k 1) :
    flattenRankBoxedRows (binaryCorrectedExtensionRows Z R) =
      permuteFamily
        (orientNewHeadPerm k (extensionCorrectedTop Z R (.inl 0) 1))
        (flattenRankBoxedRows (binaryUnorientedCorrectedExtensionRows Z R)) := by
  funext i
  rw [binaryCorrectedExtensionRows_eq_orient]
  simp only [flattenRankBoxedRows, permuteFamily]
  rw [flattenRankBoxRow_orientNewHead]

theorem castBuildRowsBin_codeEquiv_binaryCz {k : ℕ}
    (Z : RankBoxRow (ZMod 2) k 1)
    (b : Fin k → Fin k → ZMod 2)
    (hdiag : ∀ i, b i i = 0)
    (hopposite : ∀ i j, i ≠ j → b i j + b j i = 1)
    (hZ : rankBoxRowInner Z Z = 1) :
    let b' := binaryCorrectedExtensionB Z (binaryCzRankOneRows b)
    (∀ i, b' i i = 0) ∧
    (∀ i j, i ≠ j → b' i j + b' j i = 1) ∧
    CodeEquiv (castBuildRowsBin Z (binaryCzRankOneRows b))
      (binaryCzRankOneFinRows b') := by
  let R := binaryCzRankOneRows b
  let b' := binaryCorrectedExtensionB Z R
  have hflatRaw : flattenRankBoxedRows (binaryBlockExtensionRows Z R) =
      castBuildRowsBin Z R :=
    flattenRankBoxedRows_binaryBlockExtensionRows Z R
  have hflatCorr : flattenRankBoxedRows (binaryCorrectedExtensionRows Z R) =
      binaryCzRankOneFinRows b' := by
    rw [binaryCorrectedExtensionRows_eq_binaryCz Z b hdiag hZ]
    rfl
  have hrowUn :
      rowSpace (flattenRankBoxedRows
        (binaryUnorientedCorrectedExtensionRows Z R)) =
      rowSpace (flattenRankBoxedRows (binaryBlockExtensionRows Z R)) := by
    rw [rowSpace_flattenRankBoxedRows, rowSpace_flattenRankBoxedRows,
      binaryUnorientedCorrectedExtensionRows_rowSpace_eq]
  refine ⟨binaryCorrectedExtensionB_diagonal Z b hdiag,
    binaryCorrectedExtensionB_opposite Z b hdiag hopposite hZ, ?_⟩
  refine ⟨orientNewHeadPerm k (extensionCorrectedTop Z R (.inl 0) 1), ?_⟩
  change rowSpace (permuteFamily
      (orientNewHeadPerm k (extensionCorrectedTop Z R (.inl 0) 1))
      (castBuildRowsBin Z R)) = rowSpace (binaryCzRankOneFinRows b')
  rw [← hflatRaw, rowSpace_permuteFamily_eq_permutedCode,
    ← hrowUn, ← rowSpace_permuteFamily_eq_permutedCode,
    ← flatten_corrected_eq_permute_unoriented, hflatCorr]

def prependTwoPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (2 + n)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin 2)) σ).trans finSumFinEquiv)

@[simp] theorem prependTwoPerm_apply_inl {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (q : Fin 2) :
    prependTwoPerm σ (finSumFinEquiv (.inl q)) = finSumFinEquiv (.inl q) := by
  simp [prependTwoPerm]

@[simp] theorem prependTwoPerm_apply_inr {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (t : Fin n) :
    prependTwoPerm σ (finSumFinEquiv (.inr t)) =
      finSumFinEquiv (.inr (σ t)) := by
  simp [prependTwoPerm]

theorem dot_tail_inverse_permute {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x h : Fin n → ZMod 2) :
    dot x (permuteVec σ.symm h) = dot (permuteVec σ x) h := by
  have hdot := dot_coordinatePermuteLinearEquiv σ x (permuteVec σ.symm h)
  calc
    dot x (permuteVec σ.symm h) =
        dot (permuteVec σ x) (permuteVec σ (permuteVec σ.symm h)) := hdot.symm
    _ = dot (permuteVec σ x) h := by
      congr 1
      funext j
      simp [permuteVec]

theorem permuteFamily_prependTwoPerm_buildRowsBin {m n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : Fin n → ZMod 2)
    (H : Fin m → Fin n → ZMod 2) :
    permuteFamily (prependTwoPerm σ)
        (buildRowsBin x (permuteFamily σ.symm H)) =
      buildRowsBin (permuteVec σ x) H := by
  funext i j
  let p := finSumFinEquiv.symm j
  have hj : j = finSumFinEquiv p := by simp [p]
  rw [hj]
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · cases p with
    | inl q =>
        simp only [permuteFamily, permuteVec]
        rw [prependTwoPerm_apply_inl]
        fin_cases q <;> simp [buildRowsBin, r0]
    | inr t =>
        simp only [permuteFamily, permuteVec]
        rw [prependTwoPerm_apply_inr]
        simp [buildRowsBin, r0, permuteVec]
  · cases p with
    | inl q =>
        simp only [permuteFamily, permuteVec]
        rw [prependTwoPerm_apply_inl]
        fin_cases q <;>
          simp [buildRowsBin, riBin, permuteFamily, permuteVec,
            dot_tail_inverse_permute]
    | inr t =>
        simp only [permuteFamily, permuteVec]
        rw [prependTwoPerm_apply_inr]
        simp [buildRowsBin, riBin, permuteFamily, permuteVec,
          dot_tail_inverse_permute]

theorem permutedCode_symm_permutedCode {n : ℕ}
    (σ : Equiv.Perm (Fin n))
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    permutedCode σ.symm (permutedCode σ C) = C := by
  ext v
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    have heq : permuteVec σ.symm (permuteVec σ u) = u := by
      funext j
      simp [permuteVec]
    simpa [coordinatePermuteLinearEquiv, heq] using hu
  · intro hv
    refine ⟨permuteVec σ v, ⟨v, hv, rfl⟩, ?_⟩
    funext j
    simp [coordinatePermuteLinearEquiv, permuteVec]

def coordinateRelabelLinearEquiv {n m : ℕ} (e : Fin n ≃ Fin m) :
    (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2) where
  toFun v j := v (e.symm j)
  invFun w i := w (e i)
  left_inv v := by funext i; simp
  right_inv w := by funext j; simp
  map_add' u v := by rfl
  map_smul' a v := by rfl

theorem dot_coordinateRelabelLinearEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (u v : Fin n → ZMod 2) :
    dot (coordinateRelabelLinearEquiv e u)
        (coordinateRelabelLinearEquiv e v) = dot u v := by
  unfold dot coordinateRelabelLinearEquiv
  simpa using (Equiv.sum_comp e.symm (fun j : Fin n => u j * v j))

def relabelCode {n m : ℕ} (e : Fin n ≃ Fin m)
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Submodule (ZMod 2) (Fin m → ZMod 2) :=
  C.map (coordinateRelabelLinearEquiv e).toLinearMap

theorem paperSelfDualCode_relabelCode {n m : ℕ} (e : Fin n ≃ Fin m)
    {C : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (hC : paperSelfDualCode (K := ZMod 2) C) :
    paperSelfDualCode (K := ZMod 2) (relabelCode e C) := by
  have hchar :=
    (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
      (K := ZMod 2) (C := C)).mp hC
  apply (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
    (K := ZMod 2) (C := relabelCode e C)).2
  refine ⟨?_, ?_⟩
  · intro x hx
    change ∀ y ∈ relabelCode e C, dot y x = 0
    rcases hx with ⟨x₀, hx₀, rfl⟩
    intro y hy
    rcases hy with ⟨y₀, hy₀, rfl⟩
    change dot (coordinateRelabelLinearEquiv e y₀)
      (coordinateRelabelLinearEquiv e x₀) = 0
    rw [dot_coordinateRelabelLinearEquiv]
    exact hchar.1 hx₀ y₀ hy₀
  · unfold relabelCode
    rw [(coordinateRelabelLinearEquiv e).finrank_map_eq]
    have hnm : n = m := by
      have := Fintype.card_congr e
      simpa using this
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, ← hnm]
    simpa [Module.finrank_fintype_fun_eq_card] using hchar.2

def conjugatePerm {n m : ℕ} (e : Fin n ≃ Fin m)
    (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin m) :=
  e.symm.trans (σ.trans e)

theorem coordinateRelabel_permuteVec {n m : ℕ} (e : Fin n ≃ Fin m)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) :
    coordinateRelabelLinearEquiv e (permuteVec σ v) =
      permuteVec (conjugatePerm e σ) (coordinateRelabelLinearEquiv e v) := by
  funext j
  simp [coordinateRelabelLinearEquiv, permuteVec, conjugatePerm]

theorem relabelCode_permutedCode {n m : ℕ} (e : Fin n ≃ Fin m)
    (σ : Equiv.Perm (Fin n))
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    relabelCode e (permutedCode σ C) =
      permutedCode (conjugatePerm e σ) (relabelCode e C) := by
  ext w
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨coordinateRelabelLinearEquiv e v, ⟨v, hv, rfl⟩, ?_⟩
    simpa [coordinatePermuteLinearEquiv] using
      (coordinateRelabel_permuteVec e σ v).symm
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨permuteVec σ v, ⟨v, hv, rfl⟩, ?_⟩
    simpa [coordinatePermuteLinearEquiv] using
      coordinateRelabel_permuteVec e σ v

theorem relabelCode_symm_relabelCode {n m : ℕ} (e : Fin n ≃ Fin m)
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    relabelCode e.symm (relabelCode e C) = C := by
  ext v
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    simpa [coordinateRelabelLinearEquiv] using hu
  · intro hv
    refine ⟨coordinateRelabelLinearEquiv e v, ⟨v, hv, rfl⟩, ?_⟩
    funext j
    simp [coordinateRelabelLinearEquiv]

theorem permutedCode_permutedCode {n : ℕ}
    (τ σ : Equiv.Perm (Fin n))
    (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    permutedCode τ (permutedCode σ C) =
      permutedCode (τ.trans σ) C := by
  ext v
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨permuteVec σ u, ⟨u, hu, rfl⟩, rfl⟩

theorem relabel_buildRowsBin_eq_castBuildRowsBin {k : ℕ}
    (z : Fin (2 * (k + 1)) → ZMod 2)
    (b : Fin k → Fin k → ZMod 2) :
    let e : Fin (2 * ((k + 1) + 1)) ≃ Fin (2 + 2 * (k + 1)) :=
      finCongr (by omega)
    let Z := (flattenRankBoxLinearEquiv
      (K := ZMod 2) (k := k) (r := 1)).symm z
    linearEquivFamily (coordinateRelabelLinearEquiv e.symm)
        (buildRowsBin z (binaryCzRankOneFinRows b)) =
      castBuildRowsBin Z (binaryCzRankOneRows b) := by
  dsimp
  funext i j
  have hz : flattenRankBoxRow
      ((flattenRankBoxLinearEquiv
        (K := ZMod 2) (k := k) (r := 1)).symm z) = z := by
    change flattenRankBoxLinearEquiv
      ((flattenRankBoxLinearEquiv
        (K := ZMod 2) (k := k) (r := 1)).symm z) = z
    simp
  simp [linearEquivFamily, coordinateRelabelLinearEquiv,
    castBuildRowsBin, hz, binaryCzRankOneFinRows]

theorem orientedPivot_complement_tail_norm {n : ℕ}
    {C : Submodule (ZMod 2) (Fin (2 + n) → ZMod 2)}
    {x : Fin (2 + n) → ZMod 2}
    (hC : paperSelfDualCode (K := ZMod 2) C)
    (hxC : x ∈ C) (hx0 : x 0 = 0) (hx1 : x 1 = 1) :
    dot (splitTail (K := ZMod 2)
      (x + allOnes (K := ZMod 2) (2 + n)))
      (splitTail (K := ZMod 2)
        (x + allOnes (K := ZMod 2) (2 + n))) = 1 := by
  let p := x + allOnes (K := ZMod 2) (2 + n)
  let z := splitTail (K := ZMod 2) p
  have hpC : p ∈ C :=
    C.add_mem hxC (allOnes_mem_of_paperSelfDualCode hC)
  have hp0 : p 0 = 1 := by simp [p, hx0, allOnes]
  have hp1 : p 1 = 0 := by
    simp only [p, Pi.add_apply, hx1, allOnes]
    exact CharP.cast_eq_zero (ZMod 2) 2
  have hpSelf : dot p p = 0 := by
    have hpOrth : p ∈
        (dotBilin (K := ZMod 2) (n := 2 + n)).orthogonal C := hC ▸ hpC
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hpOrth) p hpC
    simpa [LinearMap.BilinForm.isOrtho_def] using h
  rw [← prepend2_head_splitTail (K := ZMod 2) p,
    dot_prepend2_prepend2, hp0, hp1] at hpSelf
  simpa [p, z, CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hpSelf

set_option maxHeartbeats 1600000 in
theorem binarySelfDualCode_has_rankOneNormalForm
    {k : ℕ}
    {C : Submodule (ZMod 2) (Fin (2 * (k + 1)) → ZMod 2)}
    (hC : paperSelfDualCode (K := ZMod 2) C) :
    HasBinaryCzRankOneNormalForm C := by
  induction k with
  | zero => exact binarySelfDualCode_has_rankOneNormalForm_lengthTwo hC
  | succ k ih =>
      let e : Fin (2 * ((k + 1) + 1)) ≃ Fin (2 + 2 * (k + 1)) :=
        finCongr (by omega)
      let Cadd := relabelCode e C
      have hCadd : paperSelfDualCode (K := ZMod 2) Cadd :=
        paperSelfDualCode_relabelCode e hC
      have hhalf :=
        (paperSelfDualCode_iff_totallyIsotropic_and_finrank_half
          (K := ZMod 2) (C := Cadd)).mp hCadd |>.2
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hhalf
      have hdim : 2 ≤ Module.finrank (ZMod 2) Cadd := by omega
      let i₀ : Fin (2 + 2 * (k + 1)) := ⟨0, by omega⟩
      obtain ⟨x, hxC, i, j, hx0, hx1⟩ :=
        exists_mem_with_zero_one_coordinates i₀ hdim
          (allOnes_mem_of_paperSelfDualCode hCadd)
      let ρ := pairToHeadPerm i j
      let C₁ := permutedCode (K := ZMod 2) ρ Cadd
      let x₁ := permuteVec ρ x
      have hpivot := pairToHeadPerm_orients_pivot hxC hx0 hx1
      have hx₁C : x₁ ∈ C₁ := by simpa [ρ, C₁, x₁] using hpivot.1
      have hx₁0 : x₁ 0 = 0 := by simpa [ρ, x₁] using hpivot.2.1
      have hx₁1 : x₁ 1 = 1 := by simpa [ρ, x₁] using hpivot.2.2
      have hC₁ : paperSelfDualCode (K := ZMod 2) C₁ :=
        paperSelfDualCode_permutedCode ρ hCadd
      let D := binaryShortenedCode C₁
      have hD : paperSelfDualCode (K := ZMod 2) D :=
        binaryShortenedCode_paperSelfDualCode hC₁ hx₁C hx₁0 hx₁1
      obtain ⟨σ, b, hdiag, hopposite, hDbox⟩ := ih hD
      let H := binaryCzRankOneFinRows b
      let G := permuteFamily σ.symm H
      have hG : rowSpace G = D := by
        rw [rowSpace_permuteFamily_eq_permutedCode, ← hDbox,
          permutedCode_symm_permutedCode]
      let p := x₁ + allOnes (K := ZMod 2) (2 + 2 * (k + 1))
      let z := splitTail (K := ZMod 2) p
      have hrec : C₁ = rowSpace (buildRowsBin z G) := by
        simpa [p, z] using
          (orientedPivot_reconstructs_from_shortening hC₁ hx₁C hx₁0 hx₁1 hG)
      let tailPerm := prependTwoPerm σ
      let z' := permuteVec σ z
      have htail : permutedCode (K := ZMod 2) tailPerm C₁ =
          rowSpace (buildRowsBin z' H) := by
        rw [hrec, ← rowSpace_permuteFamily_eq_permutedCode]
        simpa [tailPerm, z', G, H] using congrArg rowSpace
          (permuteFamily_prependTwoPerm_buildRowsBin σ z H)
      have hzNorm : dot z z = 1 := by
        simpa [p, z] using
          (orientedPivot_complement_tail_norm hC₁ hx₁C hx₁0 hx₁1)
      have hz'Norm : dot z' z' = 1 := by
        rw [show dot z' z' = dot z z by
          simpa [z'] using dot_coordinatePermuteLinearEquiv σ z z]
        exact hzNorm
      let Z := (flattenRankBoxLinearEquiv
        (K := ZMod 2) (k := k) (r := 1)).symm z'
      have hZ : rankBoxRowInner Z Z = 1 := by
        rw [← dot_flattenRankBoxRow]
        have hflat : flattenRankBoxRow Z = z' := by
          change flattenRankBoxLinearEquiv Z = z'
          simp [Z]
        rw [hflat]
        exact hz'Norm
      obtain ⟨hdiag', hopposite', ω, hω⟩ :=
        castBuildRowsBin_codeEquiv_binaryCz Z b hdiag hopposite hZ
      let b' := binaryCorrectedExtensionB Z (binaryCzRankOneRows b)
      let β := tailPerm.trans ρ
      have hcombined : permutedCode (K := ZMod 2) β Cadd =
          rowSpace (buildRowsBin z' H) := by
        rw [← permutedCode_permutedCode tailPerm ρ Cadd]
        simpa [C₁, β] using htail
      let γ := conjugatePerm e.symm β
      have hleft : relabelCode e.symm
          (permutedCode (K := ZMod 2) β Cadd) =
          permutedCode (K := ZMod 2) γ C := by
        rw [relabelCode_permutedCode]
        change permutedCode (K := ZMod 2) γ
            (relabelCode e.symm Cadd) = permutedCode γ C
        rw [show relabelCode e.symm Cadd = C by
          exact relabelCode_symm_relabelCode e C]
      have hright : relabelCode e.symm
          (rowSpace (buildRowsBin z' H)) =
          rowSpace (castBuildRowsBin Z (binaryCzRankOneRows b)) := by
        change Submodule.map (coordinateRelabelLinearEquiv e.symm).toLinearMap
            (rowSpace (buildRowsBin z' H)) = _
        rw [← rowSpace_linearEquivFamily_eq_map]
        have heq := relabel_buildRowsBin_eq_castBuildRowsBin z' b
        simpa [e, Z, H] using congrArg rowSpace heq
      have hpre : permutedCode (K := ZMod 2) γ C =
          rowSpace (castBuildRowsBin Z (binaryCzRankOneRows b)) := by
        have hback := congrArg (relabelCode e.symm) hcombined
        rw [hleft, hright] at hback
        exact hback
      refine ⟨ω.trans γ, b', hdiag', hopposite', ?_⟩
      rw [← permutedCode_permutedCode ω γ C, hpre,
        ← rowSpace_permuteFamily_eq_permutedCode]
      exact hω

end BuildingUpFormalization.Components.BinaryRankOneNormalization


