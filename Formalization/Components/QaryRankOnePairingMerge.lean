import Formalization.Components.QaryRankOnePairingMergeDefinitions
import Formalization.Components.RepeatedStepDefinitions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Formalization.Components.QaryRankBoxedNormalizationDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryRankOnePairingMerge

open Set Submodule
open BuildingUpFormalization.Components.QaryRankBoxedNormalization
open BuildingUpFormalization.Components.QaryRankOneOrientedPairing
open BuildingUpFormalization.Components.SplitBoxed
open BuildingUpFormalization.Components.RepeatedStep

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The standard product of isotropic lines has one coefficient per block. -/
theorem finrank_qaryIsotropicLineCode_exact [Fintype ι] (c : K) :
    Module.finrank K ↥(qaryIsotropicLineCode (K := K) (ι := ι) c) =
      Fintype.card ι := by
  rw [← (qaryIsotropicLineCodeLinearEquiv (K := K) (ι := ι) c).finrank_eq]
  simp

/-- Whole-block relabelling preserves the standard isotropic-line code. -/
theorem relabelBlockCode_qaryIsotropicLineCode_exact
    {κ : Type*} [Fintype ι] [Fintype κ]
    (c : K) (σ : ι ≃ κ) :
    relabelBlockCode (K := K) σ
        (qaryIsotropicLineCode (K := K) (ι := κ) c) =
      qaryIsotropicLineCode (K := K) (ι := ι) c := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change (qaryBlockDefectLinear (K := K) c) w = 0 at hw
    change (qaryBlockDefectLinear (K := K) c)
      (blockRelabelLinearEquiv (K := K) σ w) = 0
    funext i
    simpa [qaryBlockDefectLinear, blockRelabelLinearEquiv] using
      congrFun hw (σ i)
  · intro hz
    let w : QaryBlockRow K κ := fun j => z (σ.symm j)
    refine ⟨w, ?_, ?_⟩
    · change (qaryBlockDefectLinear (K := K) c) z = 0 at hz
      change (qaryBlockDefectLinear (K := K) c) w = 0
      funext j
      simpa [qaryBlockDefectLinear, w] using congrFun hz (σ.symm j)
    · funext i q
      simp [w, blockRelabelLinearEquiv]

/-- Relabelling whole blocks preserves the dimension of intersection with
the standard isotropic-line code. -/
theorem finrank_relabelBlockCode_inf_qaryIsotropicLineCode_exact
    {κ : Type*} [Fintype ι] [Fintype κ]
    (c : K) (σ : ι ≃ κ)
    (C : Submodule K (QaryBlockRow K κ)) :
    Module.finrank K
        ↥(relabelBlockCode (K := K) σ C ⊓
          qaryIsotropicLineCode (K := K) (ι := ι) c) =
      Module.finrank K
        ↥(C ⊓ qaryIsotropicLineCode (K := K) (ι := κ) c) := by
  let L := blockRelabelLinearEquiv (K := K) σ
  have hmap :
      Submodule.map L.toLinearMap
          (C ⊓ qaryIsotropicLineCode (K := K) (ι := κ) c) =
        relabelBlockCode (K := K) σ C ⊓
          qaryIsotropicLineCode (K := K) (ι := ι) c := by
    rw [Submodule.map_inf _ L.injective]
    exact congrArg (fun S => relabelBlockCode (K := K) σ C ⊓ S)
      (relabelBlockCode_qaryIsotropicLineCode_exact c σ)
  rw [← hmap]
  exact L.finrank_map_eq _

/-- The identity scalar-coordinate permutation fixes every block code. -/
theorem scalarCoordinatePermutedBlockCode_refl_exact
    {n : ℕ} (C : Submodule K (QaryBlockRow K (Fin n))) :
    scalarCoordinatePermutedBlockCode (K := K)
        (Equiv.refl (Fin n × Fin 2)) C = C := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [scalarCoordinatePermuteBlockLinearEquiv] using hw
  · intro hz
    refine ⟨z, hz, ?_⟩
    funext i q
    rfl

/-- Exact composition law for scalar-coordinate permutations.  The order is
the order in which the two code transports are performed. -/
theorem scalarCoordinatePermutedBlockCode_trans_exact
    {n : ℕ} (σ τ : Equiv.Perm (Fin n × Fin 2))
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    scalarCoordinatePermutedBlockCode (K := K) τ
        (scalarCoordinatePermutedBlockCode (K := K) σ C) =
      scalarCoordinatePermutedBlockCode (K := K) (σ.trans τ) C := by
  change Submodule.map
      (scalarCoordinatePermuteBlockLinearEquiv (K := K) τ).toLinearMap
      (Submodule.map
        (scalarCoordinatePermuteBlockLinearEquiv (K := K) σ).toLinearMap C) = _
  rw [← Submodule.map_comp]
  congr 1

/-- A whole-block relabelling is exactly the scalar-coordinate permutation
which moves both entries of each block together. -/
theorem relabelBlockCode_eq_scalarCoordinatePermutedBlockCode_exact
    {n : ℕ} (σ : Equiv.Perm (Fin n))
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    relabelBlockCode (K := K) σ C =
      scalarCoordinatePermutedBlockCode (K := K)
        (blockRelabelScalarPerm σ) C := by
  unfold relabelBlockCode scalarCoordinatePermutedBlockCode
  congr 1

/-- Existence of a rank-one oriented pairing is invariant under an arbitrary
scalar-coordinate permutation of the code. -/
theorem hasQaryRankOneOrientedPairing_scalarCoordinatePermuted_iff
    {n : ℕ} (c : K) (σ : Equiv.Perm (Fin n × Fin 2))
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    HasQaryRankOneOrientedPairing c
        (scalarCoordinatePermutedBlockCode (K := K) σ C) ↔
      HasQaryRankOneOrientedPairing c C := by
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨σ.trans τ, ?_⟩
    rw [← scalarCoordinatePermutedBlockCode_trans_exact σ τ C]
    exact hτ
  · rintro ⟨τ, hτ⟩
    refine ⟨σ.symm.trans τ, ?_⟩
    rw [scalarCoordinatePermutedBlockCode_trans_exact]
    have heq : σ.trans (σ.symm.trans τ) = τ := by
      apply Equiv.ext
      intro x
      simp
    rw [heq]
    exact hτ

/-- Existence of a rank-one oriented pairing is invariant under a
permutation of whole finite blocks. -/
theorem hasQaryRankOneOrientedPairing_relabelBlockCode_iff
    {n : ℕ} (c : K) (σ : Equiv.Perm (Fin n))
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    HasQaryRankOneOrientedPairing c (relabelBlockCode (K := K) σ C) ↔
      HasQaryRankOneOrientedPairing c C := by
  rw [relabelBlockCode_eq_scalarCoordinatePermutedBlockCode_exact]
  exact hasQaryRankOneOrientedPairing_scalarCoordinatePermuted_iff c _ C

/-- The block Kim--Lee generator is injective: the old blocks recover the
parent word and the first new coordinate then recovers the top coefficient. -/
theorem kimLeeBlockGenerator_injective
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (ell : Module.Dual K C) :
    Function.Injective (kimLeeBlockGenerator (K := K) c C ell) := by
  rintro ⟨a, z⟩ ⟨b, w⟩ h
  have hzw : z = w := by
    apply Subtype.ext
    funext i q
    have hi := congrFun (congrFun h (some i)) q
    exact hi
  subst w
  have hab := congrFun (congrFun h none) (0 : Fin 2)
  simp [kimLeeBlockGenerator, head2] at hab
  exact Prod.ext hab rfl

/-- Exact defect formula for the block Kim--Lee generator.  The new defect
is `-c*a`, independently of the Kim--Lee functional. -/
theorem qaryBlockDefectLinear_kimLeeBlockGenerator_exact
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (ell : Module.Dual K C) (az : K × C) :
    qaryBlockDefectLinear (K := K) c
        (kimLeeBlockGenerator (K := K) c C ell az) =
      fun o => match o with
        | none => -c * az.1
        | some i => blockDefectLinear c ((az.2 : QaryBlockRow K ι) i) := by
  funext o
  cases o with
  | none =>
      simp [qaryBlockDefectLinear, kimLeeBlockGenerator,
        blockDefectLinear, blockDefect, head2]
      ring
  | some i => rfl

/-- A Kim--Lee extension preserves the dimension of the intersection with
`U_c` exactly.  This is the complete nonzero-correction induction step at the
block-code level; no dimension estimate is lost. -/
theorem kimLeeBlockCode_inf_qaryIsotropicLineCode_finrank_exact
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (ell : Module.Dual K C) (hc : c ^ 2 = (-1 : K)) :
    Module.finrank K
        ↥(kimLeeBlockCode (K := K) c C ell ⊓
          qaryIsotropicLineCode (K := K) (ι := Option ι) c) =
      Module.finrank K
        ↥(C ⊓ qaryIsotropicLineCode (K := K) (ι := ι) c) := by
  let W := C ⊓ qaryIsotropicLineCode (K := K) (ι := ι) c
  let inc : W →ₗ[K] K × C :=
    (LinearMap.inr K K C).comp
      (Submodule.inclusion (show W ≤ C from inf_le_left))
  let F : W →ₗ[K] QaryBlockRow K (Option ι) :=
    (kimLeeBlockGenerator (K := K) c C ell).comp inc
  have hc0 : c ≠ 0 := by
    intro h
    simp [h] at hc
  have hrange : LinearMap.range F =
      kimLeeBlockCode (K := K) c C ell ⊓
        qaryIsotropicLineCode (K := K) (ι := Option ι) c := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨⟨inc w, rfl⟩, ?_⟩
      change qaryBlockDefectLinear (K := K) c (F w) = 0
      change qaryBlockDefectLinear (K := K) c
        (kimLeeBlockGenerator (K := K) c C ell (inc w)) = 0
      rw [qaryBlockDefectLinear_kimLeeBlockGenerator_exact c C ell]
      funext o
      cases o with
      | none => simp [inc]
      | some i =>
          have hw : qaryBlockDefectLinear (K := K) c
              (w.1 : QaryBlockRow K ι) = 0 := w.2.2
          simpa [inc, qaryBlockDefectLinear] using congrFun hw i
    · rintro ⟨⟨az, rfl⟩, hz⟩
      change qaryBlockDefectLinear (K := K) c
        (kimLeeBlockGenerator (K := K) c C ell az) = 0 at hz
      rw [qaryBlockDefectLinear_kimLeeBlockGenerator_exact c C ell] at hz
      have ha : az.1 = 0 := by
        have hhead : -c * az.1 = 0 := by
          simpa using congrFun hz none
        exact (mul_eq_zero.mp hhead).resolve_left (neg_ne_zero.mpr hc0)
      have htail : qaryBlockDefectLinear (K := K) c
          (az.2 : QaryBlockRow K ι) = 0 := by
        funext i
        simpa [qaryBlockDefectLinear] using congrFun hz (some i)
      let w : W := ⟨az.2.1, ⟨az.2.2, htail⟩⟩
      refine ⟨w, ?_⟩
      have haz : az = (0, az.2) := Prod.ext ha rfl
      rw [haz]
      rfl
  have hFinj : Function.Injective F := by
    intro w₁ w₂ h
    have hi := kimLeeBlockGenerator_injective c C ell h
    exact Subtype.ext (congrArg (fun z : K × C => (z.2 : QaryBlockRow K ι)) hi)
  rw [← hrange, LinearMap.finrank_range_of_inj hFinj]

/-- Exact `Fin (n+1) × Fin 2` Kim--Lee induction step in a fixed oriented
parent pairing. -/
theorem finKimLeeBlockCode_has_rankOne_orientedPairing_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (ell : Module.Dual K C) (hc : c ^ 2 = (-1 : K))
    (hone : Module.finrank K
      ↥(C ⊓ qaryIsotropicLineCode (K := K) c) = 1) :
    HasQaryRankOneOrientedPairing c
      (finKimLeeBlockCode (K := K) c C ell) := by
  refine ⟨Equiv.refl (Fin (n + 1) × Fin 2), ?_⟩
  rw [scalarCoordinatePermutedBlockCode_refl_exact]
  unfold finKimLeeBlockCode
  rw [finrank_relabelBlockCode_inf_qaryIsotropicLineCode_exact
    (K := K) c finSuccEquivLast (kimLeeBlockCode (K := K) c C ell)]
  rw [kimLeeBlockCode_inf_qaryIsotropicLineCode_finrank_exact c C ell hc]
  exact hone

/-- Exact defect formula for the literal block form of `buildRows`.  The new
defect forces the top-row coefficient to vanish; the old defects retain the
required `a • x` term. -/
theorem qaryBlockDefectLinear_buildingUpBlockGenerator_exact
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (x : QaryBlockRow K ι) (ell : Module.Dual K C) (az : K × C) :
    qaryBlockDefectLinear (K := K) c
        (buildingUpBlockGenerator (K := K) c C x ell az) =
      fun o => match o with
        | none => -c * az.1
        | some i => az.1 * blockDefectLinear c (x i) +
            blockDefectLinear c ((az.2 : QaryBlockRow K ι) i) := by
  funext o
  cases o with
  | none =>
      simp [qaryBlockDefectLinear, buildingUpBlockGenerator,
        blockDefectLinear, blockDefect, head2]
      ring
  | some i =>
      simp [qaryBlockDefectLinear, buildingUpBlockGenerator,
        blockDefectLinear, blockDefect]
      ring

/-- The literal building-up block generator is injective when `c` is
nonzero. -/
theorem buildingUpBlockGenerator_injective
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (x : QaryBlockRow K ι) (ell : Module.Dual K C) (hc0 : c ≠ 0) :
    Function.Injective (buildingUpBlockGenerator (K := K) c C x ell) := by
  intro u v huv
  have hnew := congrArg (blockDefectLinear (K := K) c)
    (congrFun huv none)
  have ha : u.1 = v.1 := by
    simp [buildingUpBlockGenerator, blockDefectLinear, blockDefect, head2] at hnew
    ring_nf at hnew
    exact mul_left_cancel₀ hc0 (neg_injective hnew)
  apply Prod.ext ha
  apply Subtype.ext
  funext i q
  have hold := congrFun (congrFun huv (some i)) q
  simpa [buildingUpBlockGenerator, ha] using hold

/-- The genuine building-up code preserves the isotropic intersection
dimension exactly.  No hypothesis on `x` is needed for this rank statement:
the new defect first forces its coefficient to be zero. -/
theorem buildingUpBlockCode_inf_qaryIsotropicLineCode_finrank_exact
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (x : QaryBlockRow K ι) (ell : Module.Dual K C) (hc0 : c ≠ 0) :
    Module.finrank K
        ↥(buildingUpBlockCode (K := K) c C x ell ⊓
          qaryIsotropicLineCode (K := K) (ι := Option ι) c) =
      Module.finrank K
        ↥(C ⊓ qaryIsotropicLineCode (K := K) (ι := ι) c) := by
  let W := C ⊓ qaryIsotropicLineCode (K := K) (ι := ι) c
  let inc : W →ₗ[K] K × C :=
    (LinearMap.inr K K C).comp
      (Submodule.inclusion (show W ≤ C from inf_le_left))
  let F : W →ₗ[K] QaryBlockRow K (Option ι) :=
    (buildingUpBlockGenerator (K := K) c C x ell).comp inc
  have hrange : LinearMap.range F =
      buildingUpBlockCode (K := K) c C x ell ⊓
        qaryIsotropicLineCode (K := K) (ι := Option ι) c := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨⟨inc w, rfl⟩, ?_⟩
      change qaryBlockDefectLinear (K := K) c (F w) = 0
      change qaryBlockDefectLinear (K := K) c
        (buildingUpBlockGenerator (K := K) c C x ell (inc w)) = 0
      rw [qaryBlockDefectLinear_buildingUpBlockGenerator_exact]
      funext o
      cases o with
      | none => simp [inc]
      | some i =>
          have hw : qaryBlockDefectLinear (K := K) c
              (w.1 : QaryBlockRow K ι) = 0 := w.2.2
          simpa [inc, qaryBlockDefectLinear] using congrFun hw i
    · rintro ⟨⟨az, rfl⟩, hz⟩
      change qaryBlockDefectLinear (K := K) c
        (buildingUpBlockGenerator (K := K) c C x ell az) = 0 at hz
      rw [qaryBlockDefectLinear_buildingUpBlockGenerator_exact] at hz
      have ha : az.1 = 0 := by
        have hhead : -c * az.1 = 0 := by simpa using congrFun hz none
        exact (mul_eq_zero.mp hhead).resolve_left (neg_ne_zero.mpr hc0)
      have htail : qaryBlockDefectLinear (K := K) c
          (az.2 : QaryBlockRow K ι) = 0 := by
        funext i
        simpa [qaryBlockDefectLinear, ha] using congrFun hz (some i)
      let w : W := ⟨az.2.1, ⟨az.2.2, htail⟩⟩
      refine ⟨w, ?_⟩
      have haz : az = (0, az.2) := Prod.ext ha rfl
      rw [haz]
      rfl
  have hFinj : Function.Injective F := by
    intro w₁ w₂ h
    have hi := buildingUpBlockGenerator_injective c C x ell hc0 h
    exact Subtype.ext (congrArg (fun z : K × C =>
      (z.2 : QaryBlockRow K ι)) hi)
  rw [← hrange, LinearMap.finrank_range_of_inj hFinj]

/-- Exact finite-index induction step for the literal block form of
`buildRows`. -/
theorem finBuildingUpBlockCode_has_rankOne_orientedPairing_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (x : QaryBlockRow K (Fin n)) (ell : Module.Dual K C)
    (hc0 : c ≠ 0)
    (hone : Module.finrank K
      ↥(C ⊓ qaryIsotropicLineCode (K := K) c) = 1) :
    HasQaryRankOneOrientedPairing c
      (finBuildingUpBlockCode (K := K) c C x ell) := by
  refine ⟨Equiv.refl (Fin (n + 1) × Fin 2), ?_⟩
  rw [scalarCoordinatePermutedBlockCode_refl_exact]
  unfold finBuildingUpBlockCode
  rw [finrank_relabelBlockCode_inf_qaryIsotropicLineCode_exact
    (K := K) c finSuccEquivLast
      (buildingUpBlockCode (K := K) c C x ell)]
  rw [buildingUpBlockCode_inf_qaryIsotropicLineCode_finrank_exact
    c C x ell hc0]
  exact hone

/-- Exact row-space dictionary between the scalar `buildRows` matrix and its
literal block-code generator.  This is the missing `a x + z` compatibility,
not merely an equality of dimensions. -/
theorem prependedScalarRowSpace_buildRows_eq_buildingUpBlockCode_exact
    {m n : ℕ} (x : Fin (n * 2) → K) (c : K)
    (G : Matrix (Fin m) (Fin (n * 2)) K) :
    prependedScalarRowSpaceAsBlock (buildRows x c G) =
      buildingUpBlockCode (K := K) c (scalarRowSpaceAsBlock G)
        (finScalarBlockLinearEquiv (K := K) x)
        (blockDotFunctional x (scalarRowSpaceAsBlock G)) := by
  let E := finScalarBlockLinearEquiv (K := K) (n := n)
  let E' := prependedScalarBlockLinearEquiv (K := K) (n := n)
  let C := scalarRowSpaceAsBlock G
  let ell := blockDotFunctional x C
  have hcomb (a : K) (beta : Fin m → K) :
      let z : Fin (n * 2) → K := ∑ i, beta i • G i
      let hz : z ∈ rowSpace G :=
        sum_mem (fun i _ => smul_mem _ _ (mem_rowSpace G i))
      E' (a • buildRows x c G 0 +
          ∑ i, beta i • buildRows x c G i.succ) =
        buildingUpBlockGenerator (K := K) c C (E x) ell
          (a, ⟨E z, ⟨z, hz, rfl⟩⟩) := by
    dsimp only
    have hdot : dot x (∑ i, beta i • G i) =
        ∑ i, beta i * dot x (G i) := by
      let L : (Fin (n * 2) → K) →ₗ[K] K :=
        { toFun := dot x
          map_add' := dot_add_right x
          map_smul' := fun a v => dot_smul_right a x v }
      change L (∑ i, beta i • G i) = _
      rw [map_sum]
      simp [L]
    have hell : ell
        (⟨E (∑ i, beta i • G i),
          ⟨∑ i, beta i • G i,
            sum_mem (fun i _ => smul_mem _ _ (mem_rowSpace G i)), rfl⟩⟩ : C) =
          dot x (∑ i, beta i • G i) := by
      change dot x (E.symm (E (∑ i, beta i • G i))) = _
      rw [E.symm_apply_apply]
    funext o q
    cases o with
    | none =>
      fin_cases q
      · dsimp [buildingUpBlockGenerator, head2]
        rw [hell, hdot]
        simp [E', prependedScalarBlockLinearEquiv,
          buildRows, r0, ri, prepend2, head2]
        ring
      · dsimp [buildingUpBlockGenerator, head2]
        rw [hell, hdot]
        simp [E', prependedScalarBlockLinearEquiv,
          buildRows, r0, ri, prepend2, head2]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    | some i =>
      simp [E', C, ell, prependedScalarBlockLinearEquiv,
        buildingUpBlockGenerator, buildRows, r0, ri, prepend2,
        blockDotFunctional, E, finScalarBlockLinearEquiv]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨coeff, hcoeff⟩ :=
      (Submodule.mem_span_range_iff_exists_fun K).mp hw
    rw [← hcoeff, Fin.sum_univ_succ]
    refine ⟨(coeff 0,
      ⟨E (∑ i, coeff i.succ • G i),
        ⟨∑ i, coeff i.succ • G i,
          sum_mem (fun i _ => smul_mem _ _ (mem_rowSpace G i)), rfl⟩⟩), ?_⟩
    exact (hcomb (coeff 0) (fun i => coeff i.succ)).symm
  · rintro ⟨az, rfl⟩
    rcases az.2.2 with ⟨z, hz, hzE⟩
    obtain ⟨beta, hbeta⟩ :=
      (Submodule.mem_span_range_iff_exists_fun K).mp hz
    refine ⟨az.1 • buildRows x c G 0 +
        ∑ i, beta i • buildRows x c G i.succ, ?_, ?_⟩
    · exact add_mem (smul_mem _ _ (mem_rowSpace _ 0))
        (sum_mem (fun i _ => smul_mem _ _ (mem_rowSpace _ i.succ)))
    · have hgen := (hcomb az.1 beta).symm
      have hzsub :
          (⟨E (∑ i, beta i • G i),
            ⟨∑ i, beta i • G i,
              sum_mem (fun i _ => smul_mem _ _ (mem_rowSpace G i)), rfl⟩⟩ : C) =
            az.2 := by
        apply Subtype.ext
        exact (congrArg E hbeta).trans hzE
      rw [hzsub] at hgen
      exact hgen.symm

/-- Exact row-space dictionary for the exceptional branch.  The scalar
matrix `directSumRows c G` contains the literal line `K(1,-c)`, so the sign is
retained in the conclusion. -/
theorem prependedScalarRowSpace_directSumRows_exact
    {m n : ℕ} (c : K) (G : Matrix (Fin m) (Fin (n * 2)) K) :
    prependedScalarRowSpaceAsBlock (directSumRows c G) =
      directSumBlockCode (K := K) (-c) (scalarRowSpaceAsBlock G) := by
  let E := finScalarBlockLinearEquiv (K := K) (n := n)
  let E' := prependedScalarBlockLinearEquiv (K := K) (n := n)
  let C := scalarRowSpaceAsBlock G
  have hcomb (a : K) (beta : Fin m → K) :
      let z : Fin (n * 2) → K := ∑ i, beta i • G i
      let hz : z ∈ rowSpace G :=
        sum_mem (fun i _ => smul_mem _ _ (mem_rowSpace G i))
      E' (a • directSumRows c G 0 +
          ∑ i, beta i • directSumRows c G i.succ) =
        directSumBlockGenerator (K := K) (-c) C
          (a, ⟨E z, ⟨z, hz, rfl⟩⟩) := by
    dsimp only
    funext o q
    cases o with
    | none =>
      fin_cases q
      · simp [E', prependedScalarBlockLinearEquiv,
          directSumBlockGenerator, directSumRows, prepend2, head2]
      · simp [E', prependedScalarBlockLinearEquiv,
          directSumBlockGenerator, directSumRows, prepend2, head2]
        ring
    | some i =>
      simp [E', C, prependedScalarBlockLinearEquiv,
        directSumBlockGenerator, directSumRows, prepend2,
        E, finScalarBlockLinearEquiv]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨coeff, hcoeff⟩ :=
      (Submodule.mem_span_range_iff_exists_fun K).mp hw
    rw [← hcoeff, Fin.sum_univ_succ]
    refine ⟨(coeff 0,
      ⟨E (∑ i, coeff i.succ • G i),
        ⟨∑ i, coeff i.succ • G i,
          sum_mem (fun i _ => smul_mem _ _ (mem_rowSpace G i)), rfl⟩⟩), ?_⟩
    exact (hcomb (coeff 0) (fun i => coeff i.succ)).symm
  · rintro ⟨az, rfl⟩
    rcases az.2.2 with ⟨z, hz, hzE⟩
    obtain ⟨beta, hbeta⟩ :=
      (Submodule.mem_span_range_iff_exists_fun K).mp hz
    refine ⟨az.1 • directSumRows c G 0 +
        ∑ i, beta i • directSumRows c G i.succ, ?_, ?_⟩
    · exact add_mem (smul_mem _ _ (mem_rowSpace _ 0))
        (sum_mem (fun i _ => smul_mem _ _ (mem_rowSpace _ i.succ)))
    · have hgen := (hcomb az.1 beta).symm
      have hzsub :
          (⟨E (∑ i, beta i • G i),
            ⟨∑ i, beta i • G i,
              sum_mem (fun i _ => smul_mem _ _ (mem_rowSpace G i)), rfl⟩⟩ : C) =
            az.2 := by
        apply Subtype.ext
        exact (congrArg E hbeta).trans hzE
      rw [hzsub] at hgen
      exact hgen.symm

/-- Swapping the two new scalar coordinates changes the literal summand
`K(1,-c)` into `K(1,c)`.  The equality is at code level; the scalar multiple
relating the two displayed generators is accounted for explicitly. -/
theorem headSwap_directSumBlockCode_neg_exact
    (c : K) (C : Submodule K (QaryBlockRow K ι))
    (hc : c ^ 2 = (-1 : K)) :
    Submodule.map
        (scalarCoordinateReindexBlockLinearEquiv (K := K)
          (headBlockScalarSwap (ι := ι))).toLinearMap
        (directSumBlockCode (K := K) (-c) C) =
      directSumBlockCode (K := K) c C := by
  ext w
  constructor
  · rintro ⟨_, ⟨az, rfl⟩, rfl⟩
    refine ⟨(-c * az.1, az.2), ?_⟩
    funext o q
    cases o with
    | none =>
      fin_cases q <;>
        simp [scalarCoordinateReindexBlockLinearEquiv,
          headBlockScalarSwap, directSumBlockGenerator, head2]
      rw [← mul_assoc, ← pow_two, hc]
      ring
    | some i => rfl
  · rintro ⟨az, rfl⟩
    refine ⟨directSumBlockGenerator (K := K) (-c) C (c * az.1, az.2),
      ⟨(c * az.1, az.2), rfl⟩, ?_⟩
    funext o q
    cases o with
    | none =>
      fin_cases q <;>
        simp [scalarCoordinateReindexBlockLinearEquiv,
          headBlockScalarSwap, directSumBlockGenerator, head2]
      rw [← mul_assoc, ← pow_two, hc]
      ring
    | some i => rfl

/-- Finite-index conjugation of the distinguished-block swap. -/
theorem finLastSwap_directSumBlockCode_neg_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (hc : c ^ 2 = (-1 : K)) :
    scalarCoordinatePermutedBlockCode (K := K)
        finLastBlockScalarSwap (finDirectSumBlockCode (K := K) (-c) C) =
      finDirectSumBlockCode (K := K) c C := by
  let L := blockRelabelLinearEquiv (K := K)
    (ι := Fin (n + 1)) (κ := Option (Fin n)) (finSuccEquivLast (n := n))
  let X := scalarCoordinateReindexBlockLinearEquiv (K := K)
    (headBlockScalarSwap (ι := Fin n))
  let P := scalarCoordinatePermuteBlockLinearEquiv (K := K)
    (finLastBlockScalarSwap (n := n))
  have hlinear : P.toLinearMap.comp L.toLinearMap =
      L.toLinearMap.comp X.toLinearMap := by
    ext v i q
    simp [P, L, X, finLastBlockScalarSwap,
      scalarCoordinatePermuteBlockLinearEquiv,
      blockRelabelLinearEquiv, scalarCoordinateReindexBlockLinearEquiv,
      headBlockScalarSwap]
  unfold scalarCoordinatePermutedBlockCode finDirectSumBlockCode
    relabelBlockCode
  rw [← headSwap_directSumBlockCode_neg_exact c C hc]
  change Submodule.map P.toLinearMap
      (Submodule.map L.toLinearMap (directSumBlockCode (K := K) (-c) C)) =
    Submodule.map L.toLinearMap
      (Submodule.map X.toLinearMap (directSumBlockCode (K := K) (-c) C))
  rw [← Submodule.map_comp, ← Submodule.map_comp, hlinear]

/-- Extending a parent scalar-coordinate permutation while fixing the new
block commutes exactly with the literal direct-sum construction. -/
theorem optionHeadFixed_directSumBlockCode_exact
    {n : ℕ} (d : K) (σ : Equiv.Perm (Fin n × Fin 2))
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    Submodule.map
        (scalarCoordinateReindexBlockLinearEquiv (K := K)
          (optionHeadFixedScalarPerm σ).symm).toLinearMap
        (directSumBlockCode (K := K) d C) =
      directSumBlockCode (K := K) d
        (scalarCoordinatePermutedBlockCode (K := K) σ C) := by
  let X := scalarCoordinateReindexBlockLinearEquiv (K := K)
    (optionHeadFixedScalarPerm σ).symm
  let P := scalarCoordinatePermuteBlockLinearEquiv (K := K) σ
  ext v
  constructor
  · rintro ⟨w, ⟨az, rfl⟩, rfl⟩
    let z : QaryBlockRow K (Fin n) := P az.2
    have hz : z ∈ scalarCoordinatePermutedBlockCode (K := K) σ C :=
      ⟨az.2, az.2.property, rfl⟩
    refine ⟨(az.1, ⟨z, hz⟩), ?_⟩
    funext o q
    cases o with
    | none => rfl
    | some i =>
      simp [P, z, scalarCoordinateReindexBlockLinearEquiv,
        scalarCoordinatePermuteBlockLinearEquiv,
        optionHeadFixedScalarPerm, directSumBlockGenerator]
  · rintro ⟨az, rfl⟩
    rcases az.2.property with ⟨z, hz, hzeq⟩
    refine ⟨directSumBlockGenerator (K := K) d C (az.1, ⟨z, hz⟩),
      ⟨(az.1, ⟨z, hz⟩), rfl⟩, ?_⟩
    funext o q
    cases o with
    | none => rfl
    | some i =>
      have hi := congrFun (congrFun hzeq i) q
      simpa [X, P, scalarCoordinateReindexBlockLinearEquiv,
        scalarCoordinatePermuteBlockLinearEquiv,
        optionHeadFixedScalarPerm, directSumBlockGenerator] using hi

/-- A literal split summand added to the full product of isotropic lines is
again the full product of isotropic lines. -/
theorem directSumBlockCode_qaryIsotropicLineCode_exact
    [Fintype ι] (c : K) :
    directSumBlockCode (K := K) c
        (qaryIsotropicLineCode (K := K) (ι := ι) c) =
      qaryIsotropicLineCode (K := K) (ι := Option ι) c := by
  ext v
  constructor
  · rintro ⟨az, rfl⟩
    change qaryBlockDefectLinear (K := K) c
      (directSumBlockGenerator (K := K) c
        (qaryIsotropicLineCode (K := K) (ι := ι) c) az) = 0
    funext o
    cases o with
    | none =>
      simp [qaryBlockDefectLinear, blockDefectLinear, blockDefect,
        directSumBlockGenerator, head2]
    | some i =>
      have hi : blockDefectLinear c (az.2.1 i) = 0 :=
        congrFun (show qaryBlockDefectLinear (K := K) c az.2.1 = 0
          from az.2.2) i
      simpa [qaryBlockDefectLinear, directSumBlockGenerator] using hi
  · intro hv
    change qaryBlockDefectLinear (K := K) c v = 0 at hv
    let z : QaryBlockRow K ι := fun i => v (some i)
    have hz : z ∈ qaryIsotropicLineCode (K := K) (ι := ι) c := by
      change qaryBlockDefectLinear (K := K) c z = 0
      funext i
      have hi := congrFun hv (some i)
      simpa [z, qaryBlockDefectLinear] using hi
    refine ⟨(v none 0, ⟨z, hz⟩), ?_⟩
    funext o q
    cases o with
    | none =>
      fin_cases q
      · rfl
      · have hnone := congrFun hv none
        change v none 1 - c * v none 0 = 0 at hnone
        simpa [directSumBlockGenerator, head2] using
          (sub_eq_zero.mp hnone).symm
    | some i => rfl

/-- Finite-index form of the preceding literal decomposition. -/
theorem finDirectSumBlockCode_qaryIsotropicLineCode_exact
    {n : ℕ} (c : K) :
    finDirectSumBlockCode (K := K) c
        (qaryIsotropicLineCode (K := K) (ι := Fin n) c) =
      qaryIsotropicLineCode (K := K) (ι := Fin (n + 1)) c := by
  unfold finDirectSumBlockCode
  rw [directSumBlockCode_qaryIsotropicLineCode_exact]
  exact relabelBlockCode_qaryIsotropicLineCode_exact
    (K := K) c finSuccEquivLast

/-- Finite-index form of exact naturality for the literal direct sum. -/
theorem finExtendOld_directSumBlockCode_exact
    {n : ℕ} (d : K) (σ : Equiv.Perm (Fin n × Fin 2))
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    scalarCoordinatePermutedBlockCode (K := K) (finExtendOldScalarPerm σ)
        (finDirectSumBlockCode (K := K) d C) =
      finDirectSumBlockCode (K := K) d
        (scalarCoordinatePermutedBlockCode (K := K) σ C) := by
  let L := blockRelabelLinearEquiv (K := K)
    (ι := Fin (n + 1)) (κ := Option (Fin n)) (finSuccEquivLast (n := n))
  let X := scalarCoordinateReindexBlockLinearEquiv (K := K)
    (optionHeadFixedScalarPerm σ).symm
  let P := scalarCoordinatePermuteBlockLinearEquiv (K := K)
    (finExtendOldScalarPerm σ)
  have hlinear : P.toLinearMap.comp L.toLinearMap =
      L.toLinearMap.comp X.toLinearMap := by
    ext v i q
    simp [P, L, X, finExtendOldScalarPerm,
      scalarCoordinatePermuteBlockLinearEquiv,
      blockRelabelLinearEquiv, scalarCoordinateReindexBlockLinearEquiv,
      optionHeadFixedScalarPerm]
  unfold scalarCoordinatePermutedBlockCode finDirectSumBlockCode
    relabelBlockCode
  have hoption := optionHeadFixed_directSumBlockCode_exact
    (K := K) d σ C
  unfold scalarCoordinatePermutedBlockCode at hoption
  rw [← hoption]
  change Submodule.map P.toLinearMap
      (Submodule.map L.toLinearMap (directSumBlockCode (K := K) d C)) =
    Submodule.map L.toLinearMap
      (Submodule.map X.toLinearMap (directSumBlockCode (K := K) d C))
  rw [← Submodule.map_comp, ← Submodule.map_comp, hlinear]

/-- Exact naturality of the literal building-up code.  The parent codeword
`x` is transported by the ambient permutation and the dual functional is
pulled back along the induced equivalence of the parent submodules. -/
theorem optionHeadFixed_buildingUpBlockCode_exact
    {n : ℕ} (c : K) (σ : Equiv.Perm (Fin n × Fin 2))
    (C : Submodule K (QaryBlockRow K (Fin n)))
    (x : QaryBlockRow K (Fin n)) (ell : Module.Dual K C) :
    let P := scalarCoordinatePermuteBlockLinearEquiv (K := K) σ
    let C' := scalarCoordinatePermutedBlockCode (K := K) σ C
    let E : C ≃ₗ[K] C' := P.submoduleMap C
    Submodule.map
        (scalarCoordinateReindexBlockLinearEquiv (K := K)
          (optionHeadFixedScalarPerm σ).symm).toLinearMap
        (buildingUpBlockCode (K := K) c C x ell) =
      buildingUpBlockCode (K := K) c C' (P x)
        (ell.comp E.symm.toLinearMap) := by
  dsimp only
  let X := scalarCoordinateReindexBlockLinearEquiv (K := K)
    (optionHeadFixedScalarPerm σ).symm
  let P := scalarCoordinatePermuteBlockLinearEquiv (K := K) σ
  let C' := scalarCoordinatePermutedBlockCode (K := K) σ C
  let E : C ≃ₗ[K] C' := P.submoduleMap C
  ext v
  constructor
  · rintro ⟨w, ⟨az, rfl⟩, rfl⟩
    refine ⟨(az.1, E az.2), ?_⟩
    funext o q
    cases o with
    | none =>
      fin_cases q <;>
        simp [P, E, C', scalarCoordinateReindexBlockLinearEquiv,
          optionHeadFixedScalarPerm, buildingUpBlockGenerator]
    | some i =>
      simp [P, E, C', scalarCoordinateReindexBlockLinearEquiv,
        scalarCoordinatePermuteBlockLinearEquiv,
        optionHeadFixedScalarPerm, buildingUpBlockGenerator]
      rfl
  · rintro ⟨az, rfl⟩
    refine ⟨buildingUpBlockGenerator (K := K) c C x ell
        (az.1, E.symm az.2),
      ⟨(az.1, E.symm az.2), rfl⟩, ?_⟩
    funext o q
    cases o with
    | none =>
      fin_cases q <;>
        simp [P, E, C', scalarCoordinateReindexBlockLinearEquiv,
          optionHeadFixedScalarPerm, buildingUpBlockGenerator]
    | some i =>
      simp [P, E, C', scalarCoordinateReindexBlockLinearEquiv,
        scalarCoordinatePermuteBlockLinearEquiv,
        optionHeadFixedScalarPerm, buildingUpBlockGenerator]
      have hE : E (E.symm az.2) = az.2 := E.apply_symm_apply az.2
      exact congrFun (congrFun (congrArg Subtype.val hE) i) q

/-- Finite-index naturality of the literal building-up code, including exact
transport of both its parent word and its dual functional. -/
theorem finExtendOld_buildingUpBlockCode_exact
    {n : ℕ} (c : K) (σ : Equiv.Perm (Fin n × Fin 2))
    (C : Submodule K (QaryBlockRow K (Fin n)))
    (x : QaryBlockRow K (Fin n)) (ell : Module.Dual K C) :
    let P := scalarCoordinatePermuteBlockLinearEquiv (K := K) σ
    let C' := scalarCoordinatePermutedBlockCode (K := K) σ C
    let E : C ≃ₗ[K] C' := P.submoduleMap C
    scalarCoordinatePermutedBlockCode (K := K) (finExtendOldScalarPerm σ)
        (finBuildingUpBlockCode (K := K) c C x ell) =
      finBuildingUpBlockCode (K := K) c C' (P x)
        (ell.comp E.symm.toLinearMap) := by
  dsimp only
  let L := blockRelabelLinearEquiv (K := K)
    (ι := Fin (n + 1)) (κ := Option (Fin n)) (finSuccEquivLast (n := n))
  let X := scalarCoordinateReindexBlockLinearEquiv (K := K)
    (optionHeadFixedScalarPerm σ).symm
  let P := scalarCoordinatePermuteBlockLinearEquiv (K := K)
    (finExtendOldScalarPerm σ)
  have hlinear : P.toLinearMap.comp L.toLinearMap =
      L.toLinearMap.comp X.toLinearMap := by
    ext v i q
    simp [P, L, X, finExtendOldScalarPerm,
      scalarCoordinatePermuteBlockLinearEquiv,
      blockRelabelLinearEquiv, scalarCoordinateReindexBlockLinearEquiv,
      optionHeadFixedScalarPerm]
  unfold scalarCoordinatePermutedBlockCode finBuildingUpBlockCode
    relabelBlockCode
  have hoption := optionHeadFixed_buildingUpBlockCode_exact
    (K := K) c σ C x ell
  dsimp only at hoption
  unfold scalarCoordinatePermutedBlockCode at hoption
  rw [← hoption]
  change Submodule.map P.toLinearMap
      (Submodule.map L.toLinearMap
        (buildingUpBlockCode (K := K) c C x ell)) =
    Submodule.map L.toLinearMap
      (Submodule.map X.toLinearMap
        (buildingUpBlockCode (K := K) c C x ell))
  rw [← Submodule.map_comp, ← Submodule.map_comp, hlinear]

/-- Exact coefficient-elimination bridge.

If a linear relation among a selected parent defect column `e` and the
remaining columns `d i` has nonzero coefficient at `e`, then `e` lies in the
span of the remaining columns.  This is the precise right-kernel calculation
needed before applying the cross-pair merge lemma. -/
theorem parent_defect_relation_head_mem_span_exact
    [Fintype ι] (d : ι → V) (e : V) (coeff : Option ι → K)
    (hcoeff : coeff none ≠ 0)
    (hrel : ∑ j, coeff j • parentDefectFamily d e j = 0) :
    e ∈ span K (range d) := by
  classical
  have htail : (∑ i, coeff (some i) • d i) ∈ span K (range d) :=
    sum_mem (fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩))
  have hsplit : coeff none • e + ∑ i, coeff (some i) • d i = 0 := by
    simpa [Fintype.sum_option, parentDefectFamily] using hrel
  have hhead : coeff none • e ∈ span K (range d) := by
    rw [eq_neg_of_add_eq_zero_left hsplit]
    exact neg_mem htail
  have hinv := smul_mem (span K (range d)) (coeff none)⁻¹ hhead
  simpa [smul_smul, hcoeff] using hinv

/-- Exact selection theorem for a corank-one defect family.

If the span of a finite family has dimension one less than the number of
columns, one column can be selected so that its coefficient in a relation is
nonzero and all complementary columns are linearly independent. -/
theorem exists_selected_defect_relation_of_corank_one_exact
    [Fintype ι] [DecidableEq ι] (f : ι → V)
    (hcorank : Module.finrank K (span K (range f)) + 1 = Fintype.card ι) :
    ∃ i : ι, ∃ coeff : Option {j : ι // j ≠ i} → K,
      coeff none ≠ 0 ∧
      (∑ o, coeff o •
        parentDefectFamily (fun j : {j : ι // j ≠ i} => f j) (f i) o = 0) ∧
      LinearIndependent K (fun j : {j : ι // j ≠ i} => f j) := by
  classical
  have hnotli : ¬ LinearIndependent K f := by
    intro hli
    have hdim := finrank_span_eq_card hli
    omega
  obtain ⟨coeffFull, hrelFull, i, hi⟩ :=
    Fintype.not_linearIndependent_iff.mp hnotli
  let e : Option {j : ι // j ≠ i} ≃ ι := Equiv.optionSubtypeNe i
  let coeff : Option {j : ι // j ≠ i} → K :=
    fun o => coeffFull (e o)
  let d : {j : ι // j ≠ i} → V := fun j => f j
  have hcoeff : coeff none ≠ 0 := by
    simpa [coeff, e] using hi
  have hrel : ∑ o, coeff o • parentDefectFamily d (f i) o = 0 := by
    have hreindex : (∑ o, coeffFull (e o) • f (e o)) = 0 := by
      exact (e.sum_comp (fun j => coeffFull j • f j)).trans hrelFull
    simpa [coeff, d, e, parentDefectFamily] using hreindex
  have hselected : f i ∈ span K (range d) :=
    parent_defect_relation_head_mem_span_exact d (f i) coeff hcoeff hrel
  have hspan : span K (range d) = span K (range f) := by
    apply le_antisymm
    · apply span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact subset_span ⟨j, rfl⟩
    · apply span_le.mpr
      rintro _ ⟨j, rfl⟩
      by_cases hji : j = i
      · simpa [hji] using hselected
      · exact subset_span ⟨⟨j, hji⟩, rfl⟩
  have hcard : Fintype.card {j : ι // j ≠ i} + 1 = Fintype.card ι := by
    simpa [e] using Fintype.card_congr e
  have hdimTail :
      Module.finrank K (span K (range d)) =
        Fintype.card {j : ι // j ≠ i} := by
    rw [hspan]
    omega
  have hd : LinearIndependent K d := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    exact hdimTail.symm
  exact ⟨i, coeff, hcoeff, hrel, hd⟩

/-- Exact cross-pair merge lemma for the rank-one induction.

After one dependent parent defect column has been removed, let `d` be the
remaining independent family.  If that removed column has the form
`a + c • b` and lies in the span of `d`, then cross-pairing the two new
coordinates with that parent pair raises the defect rank by exactly one.
The complete child family has two new columns, but only one new independent
direction. -/
theorem paper_qary_rankOne_crossPair_merge_exact
    [Fintype ι] (c : K) (d : ι → V) (a b : V)
    (hc : c ≠ 0) (hd : LinearIndependent K d)
    (hdep : a + c • b ∈ span K (range d)) :
    Module.finrank K (span K (range (crossPairDefects c d a b))) =
      Fintype.card ι + 1 := by
  classical
  let lift : V →ₗ[K] K × V := LinearMap.inr K K V
  have hlift : LinearIndependent K (fun i => liftedDefect (K := K) (d i)) := by
    simpa [lift, liftedDefect, Function.comp_def] using
      hd.map' lift (by simp [lift])
  have hfirst_not_mem :
      firstCrossDefect c a ∉
        span K (range (fun i => liftedDefect (K := K) (d i))) := by
    intro hmem
    have hker : span K (range (fun i => liftedDefect (K := K) (d i))) ≤
        LinearMap.ker (LinearMap.fst K K V) := by
      apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      simp [liftedDefect]
    have hz := hker hmem
    exact hc (neg_eq_zero.mp (by simpa [firstCrossDefect] using hz))
  have hbasis : LinearIndependent K (crossPairBasis c d a) := by
    let basis' : Option ι → K × V := fun o =>
      Option.casesOn' o (firstCrossDefect c a)
        (fun i => liftedDefect (K := K) (d i))
    have hbasis' : LinearIndependent K basis' :=
      hlift.option hfirst_not_mem
    have heq : basis' = crossPairBasis c d a := by
      funext o
      cases o <;> rfl
    simpa [heq] using hbasis'
  have hlift_dep : liftedDefect (K := K) (a + c • b) ∈
      span K (range (fun i => liftedDefect (K := K) (d i))) := by
    have hm : lift (a + c • b) ∈ (span K (range d)).map lift :=
      Submodule.mem_map_of_mem (f := lift) hdep
    rw [Submodule.map_span] at hm
    have himage : lift '' range d =
        range (fun i => liftedDefect (K := K) (d i)) := by
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, by simp [lift, liftedDefect]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨d i, ⟨i, rfl⟩, by simp [lift, liftedDefect]⟩
    rw [himage] at hm
    simpa [lift, liftedDefect, Function.comp_def] using hm
  have hlift_span_le : span K (range (fun i => liftedDefect (K := K) (d i))) ≤
      span K (range (crossPairBasis c d a)) := by
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact subset_span ⟨some i, rfl⟩
  have hdep_basis : liftedDefect (K := K) (a + c • b) ∈
      span K (range (crossPairBasis c d a)) :=
    hlift_span_le hlift_dep
  have hfirst_basis : firstCrossDefect c a ∈
      span K (range (crossPairBasis c d a)) :=
    subset_span ⟨none, rfl⟩
  have hsecond_basis : secondCrossDefect b ∈
      span K (range (crossPairBasis c d a)) := by
    have hsub := sub_mem hdep_basis hfirst_basis
    have hscaled := smul_mem (span K (range (crossPairBasis c d a))) c⁻¹ hsub
    convert hscaled using 1
    all_goals simp [liftedDefect, firstCrossDefect, secondCrossDefect, hc]
  have hspan : span K (range (crossPairDefects c d a b)) =
      span K (range (crossPairBasis c d a)) := by
    apply le_antisymm
    · apply span_le.mpr
      rintro _ ⟨j, rfl⟩
      cases j with
      | none => exact hsecond_basis
      | some j => exact subset_span ⟨j, rfl⟩
    · apply span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact subset_span ⟨some j, rfl⟩
  rw [hspan, finrank_span_eq_card hbasis]
  simp

/-- Exact parent-relation form of the cross-pair merge.

The selected parent defect is `b - c • a`.  Under `c² = -1`, its companion
column needed by the cross-pair calculation is
`a + c • b = c • (b - c • a)`.  A relation with nonzero selected
coefficient therefore supplies exactly the span hypothesis of
`paper_qary_rankOne_crossPair_merge_exact`. -/
theorem paper_qary_rankOne_crossPair_merge_of_parent_relation_exact
    [Fintype ι] (c : K) (d : ι → V) (a b : V)
    (coeff : Option ι → K)
    (hc : c ^ 2 = (-1 : K)) (hd : LinearIndependent K d)
    (hcoeff : coeff none ≠ 0)
    (hrel : ∑ j, coeff j •
      parentDefectFamily d (b - c • a) j = 0) :
    Module.finrank K (span K (range (crossPairDefects c d a b))) =
      Fintype.card ι + 1 := by
  have hdef : b - c • a ∈ span K (range d) :=
    parent_defect_relation_head_mem_span_exact d (b - c • a)
      coeff hcoeff hrel
  have hcc : c * c = (-1 : K) := by
    simpa [pow_two] using hc
  have hcompanion : a + c • b = c • (b - c • a) := by
    calc
      a + c • b = c • b - (-1 : K) • a := by simp [add_comm]
      _ = c • b - (c * c) • a := by rw [hcc]
      _ = c • (b - c • a) := by rw [smul_sub, smul_smul]
  have hdep : a + c • b ∈ span K (range d) := by
    rw [hcompanion]
    exact smul_mem _ c hdef
  have hc0 : c ≠ 0 := by
    intro h
    simp [h] at hc
  exact paper_qary_rankOne_crossPair_merge_exact c d a b hc0 hd hdep

/-- The abstract cross-pair defect family is literally the defect family of
the cross-paired direct sum `K(1,c) ⊕ C₀`. -/
theorem crossPairedDirectSumDefects_eq_crossPairDefects
    (c : K) (d : ι → V) (a b : V) (hc : c ^ 2 = (-1 : K)) :
    crossPairedDirectSumDefects c d a b = crossPairDefects c d a b := by
  funext o
  cases o with
  | none =>
      have hcc : c * c = (-1 : K) := by simpa [pow_two] using hc
      simp [crossPairedDirectSumDefects, crossPairDefects,
        generatorColumnPairDefect, directSumCompanionColumn,
        liftedParentColumn, secondCrossDefect, hcc]
  | some o =>
      cases o <;>
        simp [crossPairedDirectSumDefects, crossPairDefects, crossPairBasis,
          generatorColumnPairDefect, directSumHeadColumn, liftedParentColumn,
          firstCrossDefect]

/-- Exact corank-one direct-sum branch at the defect-matrix level.

For parent generator-column pairs `(a i,b i)`, corank one of the parent
defect family permits a selected pair whose cross-paired direct sum has defect
rank exactly one larger. -/
theorem exists_crossPaired_directSum_defect_rank_of_corank_one_exact
    [Fintype ι] [DecidableEq ι] (c : K) (a b : ι → V)
    (hc : c ^ 2 = (-1 : K))
    (hcorank : Module.finrank K
      (span K (range (fun i => b i - c • a i))) + 1 = Fintype.card ι) :
    ∃ i : ι,
      let d := fun j : {j : ι // j ≠ i} => b j - c • a j
      Module.finrank K
        (span K (range (crossPairedDirectSumDefects c d (a i) (b i)))) =
          Fintype.card {j : ι // j ≠ i} + 1 := by
  let f : ι → V := fun i => b i - c • a i
  obtain ⟨i, coeff, hcoeff, hrel, hd⟩ :=
    exists_selected_defect_relation_of_corank_one_exact f hcorank
  refine ⟨i, ?_⟩
  dsimp only
  let d : {j : ι // j ≠ i} → V := fun j => b j - c • a j
  change Module.finrank K
      (span K (range (crossPairedDirectSumDefects c d (a i) (b i)))) =
        Fintype.card {j : ι // j ≠ i} + 1
  have hrel' : ∑ o, coeff o •
      parentDefectFamily d (b i - c • a i) o = 0 := by
    simpa [f, d] using hrel
  have hd' : LinearIndependent K d := by
    simpa [f, d] using hd
  have hrank := paper_qary_rankOne_crossPair_merge_of_parent_relation_exact
    c d (a i) (b i) coeff hc hd' hcoeff hrel'
  rw [crossPairedDirectSumDefects_eq_crossPairDefects c d (a i) (b i) hc]
  exact hrank

/-- Exact rank--nullity bridge for a square finite column family.

If the column span has codimension one in an ambient space whose dimension
equals the number of columns, then the kernel of the dual evaluation map is
one-dimensional. -/
theorem columnEvaluationDual_kernel_finrank_one_exact
    [Fintype ι] [FiniteDimensional K V] (v : ι → V)
    (hsquare : Module.finrank K V = Fintype.card ι)
    (hcorank : Module.finrank K (span K (range v)) + 1 = Fintype.card ι) :
    Module.finrank K (LinearMap.ker (columnEvaluationDual (K := K) v)) = 1 := by
  let synthesis : (ι → K) →ₗ[K] V := Fintype.linearCombination K v
  have hrange : Module.finrank K (LinearMap.range synthesis) + 1 =
      Fintype.card ι := by
    change Module.finrank K
        (LinearMap.range (Fintype.linearCombination K v)) + 1 = Fintype.card ι
    rw [Fintype.range_linearCombination]
    exact hcorank
  have hdualRange :
      Module.finrank K (LinearMap.range (columnEvaluationDual (K := K) v)) =
        Module.finrank K (LinearMap.range synthesis) := by
    simpa only [columnEvaluationDual, synthesis] using
      LinearMap.finrank_range_dualMap_eq_finrank_range synthesis
  have hrankNullity :=
    LinearMap.finrank_range_add_finrank_ker (columnEvaluationDual (K := K) v)
  have hdomain : Module.finrank K (Module.Dual K V) = Fintype.card ι := by
    rw [Subspace.dual_finrank_eq, hsquare]
  rw [hdualRange, hdomain] at hrankNullity
  omega

/-- Exact nullity-one direct-sum branch for the defect evaluation map.

Under the square ambient-dimension hypothesis, the selected cross-paired
direct sum supplied by the corank-one merge theorem has a one-dimensional
dual defect kernel. -/
theorem exists_crossPaired_directSum_defect_nullity_one_exact
    [Fintype ι] [DecidableEq ι] [FiniteDimensional K V]
    (c : K) (a b : ι → V)
    (hc : c ^ 2 = (-1 : K))
    (hsquare : Module.finrank K V = Fintype.card ι)
    (hcorank : Module.finrank K
      (span K (range (fun i => b i - c • a i))) + 1 = Fintype.card ι) :
    ∃ i : ι,
      let d := fun j : {j : ι // j ≠ i} => b j - c • a j
      Module.finrank K (LinearMap.ker
        (columnEvaluationDual (K := K)
          (crossPairedDirectSumDefects c d (a i) (b i)))) = 1 := by
  obtain ⟨i, hrank⟩ :=
    exists_crossPaired_directSum_defect_rank_of_corank_one_exact
      c a b hc hcorank
  refine ⟨i, ?_⟩
  dsimp only
  let J := {j : ι // j ≠ i}
  let d : J → V := fun j => b j - c • a j
  let defects : Option (Option J) → K × V :=
    crossPairedDirectSumDefects c d (a i) (b i)
  change Module.finrank K
      (LinearMap.ker (columnEvaluationDual (K := K) defects)) = 1
  apply columnEvaluationDual_kernel_finrank_one_exact defects
  · have hcardJ : Fintype.card J + 1 = Fintype.card ι := by
      let e : Option J ≃ ι := Equiv.optionSubtypeNe i
      simpa [J] using Fintype.card_congr e
    simp only [Module.finrank_prod, Module.finrank_self, Fintype.card_option]
    omega
  · have hrank' : Module.finrank K (span K (range defects)) =
        Fintype.card J + 1 := by
      simpa [J, d, defects] using hrank
    rw [hrank']
    simp only [Fintype.card_option]

/-- Exact passage from defect-column corank to the intersection of a generated
block code with `U_c`.

The injectivity hypothesis is precisely row independence of the displayed
generator: it prevents coefficient-kernel vectors from being lost when they
are mapped into the code. -/
theorem blockColumnGenerator_intersection_finrank_one_exact
    [Fintype ι] [FiniteDimensional K V]
    (c : K) (x y : ι → V)
    (hgen : Function.Injective (blockColumnGenerator (K := K) x y))
    (hsquare : Module.finrank K V = Fintype.card ι)
    (hcorank : Module.finrank K
      (span K (range (fun i => y i - c • x i))) + 1 = Fintype.card ι) :
    Module.finrank K
      ↥((LinearMap.range (blockColumnGenerator (K := K) x y) :
          Submodule K (QaryBlockRow K ι)) ⊓
        qaryIsotropicLineCode (K := K) c) = 1 := by
  classical
  let defects : ι → V := fun i => y i - c • x i
  let eval : Module.Dual K V →ₗ[K] (ι → K) :=
    columnEvaluation (K := K) defects
  let evalDual : Module.Dual K V →ₗ[K] Module.Dual K (ι → K) :=
    columnEvaluationDual (K := K) defects
  let gen : Module.Dual K V →ₗ[K] QaryBlockRow K ι :=
    blockColumnGenerator (K := K) x y
  have hker : LinearMap.ker eval = LinearMap.ker evalDual := by
    ext phi
    constructor
    · intro hphi
      rw [LinearMap.mem_ker] at hphi ⊢
      apply LinearMap.ext
      intro coeff
      have hcoord : ∀ i, phi (defects i) = 0 := by
        intro i
        have := congrFun hphi i
        simpa [eval, columnEvaluation] using this
      simp [evalDual, columnEvaluationDual, Fintype.linearCombination,
        hcoord]
    · intro hphi
      rw [LinearMap.mem_ker] at hphi ⊢
      funext i
      have hi := LinearMap.congr_fun hphi (Pi.single i 1)
      simpa [eval, evalDual, columnEvaluation, columnEvaluationDual,
        Fintype.linearCombination, Pi.single_apply] using hi
  have hcomp :
      (qaryBlockDefectLinear (K := K) (ι := ι) c).comp gen = eval := by
    ext phi i
    simp [gen, eval, defects, blockColumnGenerator, columnEvaluation,
      qaryBlockDefectLinear, blockDefectLinear, blockDefect, head2]
  have hmap : Submodule.map gen (LinearMap.ker eval) =
      LinearMap.range gen ⊓ qaryIsotropicLineCode (K := K) c := by
    ext z
    constructor
    · rintro ⟨phi, hphi, rfl⟩
      refine ⟨⟨phi, rfl⟩, ?_⟩
      change ((qaryBlockDefectLinear (K := K) c).comp gen) phi = 0
      have hzero : eval phi = 0 := hphi
      rw [hcomp]
      exact hzero
    · rintro ⟨⟨phi, rfl⟩, hz⟩
      refine ⟨phi, ?_, rfl⟩
      change eval phi = 0
      rw [← hcomp]
      exact hz
  have hmapFinrank : Module.finrank K (Submodule.map gen (LinearMap.ker eval)) =
      Module.finrank K (LinearMap.ker eval) := by
    rw [← LinearMap.range_domRestrict]
    apply LinearMap.finrank_range_of_inj
    intro phi psi h
    apply Subtype.ext
    exact hgen h
  rw [← hmap, hmapFinrank, hker]
  apply columnEvaluationDual_kernel_finrank_one_exact defects hsquare
  simpa [defects] using hcorank

/-- Exact rank--nullity identity for an injective block-column generator.

The rank of the defect columns plus the dimension of the generated code's
intersection with `U_c` equals the coefficient-space dimension. -/
theorem blockColumnGenerator_defect_rank_add_intersection_finrank_exact
    [Fintype ι] [FiniteDimensional K V]
    (c : K) (x y : ι → V)
    (hgen : Function.Injective (blockColumnGenerator (K := K) x y)) :
    Module.finrank K (span K (range (fun i => y i - c • x i))) +
      Module.finrank K
        ↥((LinearMap.range (blockColumnGenerator (K := K) x y) :
            Submodule K (QaryBlockRow K ι)) ⊓
          qaryIsotropicLineCode (K := K) c) =
      Module.finrank K V := by
  classical
  let defects : ι → V := fun i => y i - c • x i
  let synthesis : (ι → K) →ₗ[K] V := Fintype.linearCombination K defects
  let eval : Module.Dual K V →ₗ[K] (ι → K) :=
    columnEvaluation (K := K) defects
  let evalDual : Module.Dual K V →ₗ[K] Module.Dual K (ι → K) :=
    columnEvaluationDual (K := K) defects
  let gen : Module.Dual K V →ₗ[K] QaryBlockRow K ι :=
    blockColumnGenerator (K := K) x y
  have hdualRange : Module.finrank K (LinearMap.range evalDual) =
      Module.finrank K (span K (range defects)) := by
    calc
      Module.finrank K (LinearMap.range evalDual) =
          Module.finrank K (LinearMap.range synthesis) := by
            simpa only [evalDual, columnEvaluationDual, synthesis] using
              LinearMap.finrank_range_dualMap_eq_finrank_range synthesis
      _ = Module.finrank K (span K (range defects)) := by
            change Module.finrank K
              (LinearMap.range (Fintype.linearCombination K defects)) = _
            rw [Fintype.range_linearCombination]
  have hker : LinearMap.ker eval = LinearMap.ker evalDual := by
    ext phi
    constructor
    · intro hphi
      rw [LinearMap.mem_ker] at hphi ⊢
      apply LinearMap.ext
      intro coeff
      have hcoord : ∀ i, phi (defects i) = 0 := by
        intro i
        have := congrFun hphi i
        simpa [eval, columnEvaluation] using this
      simp [evalDual, columnEvaluationDual, Fintype.linearCombination,
        hcoord]
    · intro hphi
      rw [LinearMap.mem_ker] at hphi ⊢
      funext i
      have hi := LinearMap.congr_fun hphi (Pi.single i 1)
      simpa [eval, evalDual, columnEvaluation, columnEvaluationDual,
        Fintype.linearCombination, Pi.single_apply] using hi
  have hcomp :
      (qaryBlockDefectLinear (K := K) (ι := ι) c).comp gen = eval := by
    ext phi i
    simp [gen, eval, defects, blockColumnGenerator, columnEvaluation,
      qaryBlockDefectLinear, blockDefectLinear, blockDefect, head2]
  have hmap : Submodule.map gen (LinearMap.ker eval) =
      LinearMap.range gen ⊓ qaryIsotropicLineCode (K := K) c := by
    ext z
    constructor
    · rintro ⟨phi, hphi, rfl⟩
      refine ⟨⟨phi, rfl⟩, ?_⟩
      change ((qaryBlockDefectLinear (K := K) c).comp gen) phi = 0
      rw [hcomp]
      exact hphi
    · rintro ⟨⟨phi, rfl⟩, hz⟩
      refine ⟨phi, ?_, rfl⟩
      change eval phi = 0
      rw [← hcomp]
      exact hz
  have hmapFinrank : Module.finrank K (Submodule.map gen (LinearMap.ker eval)) =
      Module.finrank K (LinearMap.ker eval) := by
    rw [← LinearMap.range_domRestrict]
    apply LinearMap.finrank_range_of_inj
    intro phi psi h
    apply Subtype.ext
    exact hgen h
  have hintersection : Module.finrank K
        ↥((LinearMap.range gen : Submodule K (QaryBlockRow K ι)) ⊓
          qaryIsotropicLineCode (K := K) c) =
      Module.finrank K (LinearMap.ker evalDual) := by
    rw [← hmap, hmapFinrank, hker]
  have hrankNullity := LinearMap.finrank_range_add_finrank_ker evalDual
  rw [hdualRange, ← hintersection, Subspace.dual_finrank_eq] at hrankNullity
  simpa [defects, gen] using hrankNullity

/-- The defect columns of the literal cross-paired child are exactly the
abstract direct-sum defect family used in the rank calculation. -/
theorem crossPairedDirectSumColumns_defect_eq
    (c : K) (a b : ι → V) (i : ι) (hc : c ^ 2 = (-1 : K)) :
    (fun o => crossPairedDirectSumSecondColumns (K := K) a b i o -
      c • crossPairedDirectSumFirstColumns (K := K) c a i o) =
      crossPairedDirectSumDefects c
        (fun j : {j : ι // j ≠ i} => b j - c • a j) (a i) (b i) := by
  funext o
  have hcc : c * c = (-1 : K) := by simpa [pow_two] using hc
  cases o with
  | none =>
      simp [crossPairedDirectSumFirstColumns,
        crossPairedDirectSumSecondColumns, crossPairedDirectSumDefects,
        generatorColumnPairDefect, directSumCompanionColumn,
        liftedParentColumn, hcc]
  | some o =>
      cases o <;>
        simp [crossPairedDirectSumFirstColumns,
          crossPairedDirectSumSecondColumns, crossPairedDirectSumDefects,
          generatorColumnPairDefect, directSumHeadColumn, liftedParentColumn,
          liftedDefect]

/-- Cross-pairing a split direct summand with one parent block preserves
injectivity of the block-column generator. -/
theorem crossPairedDirectSum_blockColumnGenerator_injective
    (c : K) (a b : ι → V) (i : ι)
    (hparent : Function.Injective (blockColumnGenerator (K := K) a b)) :
    Function.Injective
      (blockColumnGenerator (K := K)
        (crossPairedDirectSumFirstColumns (K := K) c a i)
        (crossPairedDirectSumSecondColumns (K := K) a b i)) := by
  classical
  intro phi psi hphiPsi
  let inr : V →ₗ[K] K × V := LinearMap.inr K K V
  let phiV : Module.Dual K V := phi.comp inr
  let psiV : Module.Dual K V := psi.comp inr
  have hhead : phi (1, 0) = psi (1, 0) := by
    have h := congrFun (congrFun hphiPsi (some none)) (0 : Fin 2)
    simpa [blockColumnGenerator, crossPairedDirectSumFirstColumns,
      directSumHeadColumn, head2] using h
  have hparentImages :
      blockColumnGenerator (K := K) a b phiV =
        blockColumnGenerator (K := K) a b psiV := by
    funext j q
    by_cases hji : j = i
    · subst j
      fin_cases q
      · have h := congrFun (congrFun hphiPsi (some none)) (1 : Fin 2)
        simpa [blockColumnGenerator, crossPairedDirectSumSecondColumns,
          liftedParentColumn, phiV, psiV, inr, head2] using h
      · have h := congrFun (congrFun hphiPsi none) (1 : Fin 2)
        simpa [blockColumnGenerator, crossPairedDirectSumSecondColumns,
          liftedParentColumn, phiV, psiV, inr, head2] using h
    · fin_cases q
      · have h := congrFun (congrFun hphiPsi (some (some ⟨j, hji⟩)))
          (0 : Fin 2)
        simpa [blockColumnGenerator, crossPairedDirectSumFirstColumns,
          liftedParentColumn, phiV, psiV, inr, head2] using h
      · have h := congrFun (congrFun hphiPsi (some (some ⟨j, hji⟩)))
          (1 : Fin 2)
        simpa [blockColumnGenerator, crossPairedDirectSumSecondColumns,
          liftedParentColumn, phiV, psiV, inr, head2] using h
  have hV : phiV = psiV := hparent hparentImages
  apply LinearMap.ext
  rintro ⟨t, v⟩
  have hdecomp : (t, v) = t • (1, 0) + inr v := by
    ext <;> simp [inr]
  have hv : phi (inr v) = psi (inr v) := by
    have := LinearMap.congr_fun hV v
    simpa [phiV, psiV] using this
  rw [hdecomp, map_add, map_add, map_smul, map_smul, hhead, hv]

/-- Exact direct-sum branch at the generated-code level.

For a square injective parent generator with corank-one defect family, one
selected cross-pairing of the split direct summand produces a child code whose
intersection with `U_c` is one-dimensional. -/
theorem exists_crossPaired_directSum_code_intersection_finrank_one_exact
    [Fintype ι] [DecidableEq ι] [FiniteDimensional K V]
    (c : K) (a b : ι → V)
    (hc : c ^ 2 = (-1 : K))
    (hparent : Function.Injective (blockColumnGenerator (K := K) a b))
    (hsquare : Module.finrank K V = Fintype.card ι)
    (hcorank : Module.finrank K
      (span K (range (fun i => b i - c • a i))) + 1 = Fintype.card ι) :
    ∃ i : ι,
      let xChild := crossPairedDirectSumFirstColumns (K := K) c a i
      let yChild := crossPairedDirectSumSecondColumns (K := K) a b i
      Module.finrank K
        ↥((LinearMap.range (blockColumnGenerator (K := K) xChild yChild) :
            Submodule K (QaryBlockRow K (Option (Option {j : ι // j ≠ i})))) ⊓
          qaryIsotropicLineCode (K := K) c) = 1 := by
  obtain ⟨i, hrank⟩ :=
    exists_crossPaired_directSum_defect_rank_of_corank_one_exact
      c a b hc hcorank
  refine ⟨i, ?_⟩
  dsimp only
  let J := {j : ι // j ≠ i}
  let xChild : Option (Option J) → K × V :=
    crossPairedDirectSumFirstColumns (K := K) c a i
  let yChild : Option (Option J) → K × V :=
    crossPairedDirectSumSecondColumns (K := K) a b i
  change Module.finrank K
      ↥((LinearMap.range (blockColumnGenerator (K := K) xChild yChild) :
          Submodule K (QaryBlockRow K (Option (Option J)))) ⊓
        qaryIsotropicLineCode (K := K) c) = 1
  apply blockColumnGenerator_intersection_finrank_one_exact c xChild yChild
  · exact crossPairedDirectSum_blockColumnGenerator_injective c a b i hparent
  · have hcardJ : Fintype.card J + 1 = Fintype.card ι := by
      let e : Option J ≃ ι := Equiv.optionSubtypeNe i
      simpa [J] using Fintype.card_congr e
    simp only [Module.finrank_prod, Module.finrank_self, Fintype.card_option]
    omega
  · have hdefects : (fun o => yChild o - c • xChild o) =
        crossPairedDirectSumDefects c
          (fun j : J => b j - c • a j) (a i) (b i) := by
      simpa [J, xChild, yChild] using
        crossPairedDirectSumColumns_defect_eq c a b i hc
    rw [hdefects]
    have hrank' : Module.finrank K
        (span K (range (crossPairedDirectSumDefects c
          (fun j : J => b j - c • a j) (a i) (b i)))) =
          Fintype.card J + 1 := by
      simpa [J] using hrank
    rw [hrank']
    simp only [Fintype.card_option]

/-- Exact canonical bidual realization of an arbitrary finite block code.

The restricted scalar-coordinate functionals recover every codeword through
the natural equivalence `C ≃ C**`.  Consequently the canonical generator is
injective and its range is literally `C`, not merely an equivalent code. -/
theorem canonicalBlockCodeGenerator_exact
    [Fintype ι] (C : Submodule K (QaryBlockRow K ι)) :
    Function.Injective (canonicalBlockCodeGenerator (K := K) C) ∧
      LinearMap.range (canonicalBlockCodeGenerator (K := K) C) = C := by
  let e : C ≃ₗ[K] Module.Dual K (Module.Dual K C) := Module.evalEquiv K C
  let gen : Module.Dual K (Module.Dual K C) →ₗ[K] QaryBlockRow K ι :=
    canonicalBlockCodeGenerator (K := K) C
  have heval : ∀ z : C, gen (e z) = (z : QaryBlockRow K ι) := by
    intro z
    funext i q
    fin_cases q <;>
      simp [gen, e, canonicalBlockCodeGenerator, blockColumnGenerator,
        blockCodeFirstCoordinate, blockCodeSecondCoordinate, head2,
        Module.Dual.eval_apply]
  have happly : ∀ phi, gen phi =
      ((e.symm phi : C) : QaryBlockRow K ι) := by
    intro phi
    rw [← heval (e.symm phi), e.apply_symm_apply]
  constructor
  · intro phi psi h
    apply e.symm.injective
    apply Subtype.ext
    rw [happly phi, happly psi] at h
    exact h
  · ext z
    constructor
    · rintro ⟨phi, rfl⟩
      rw [happly]
      exact (e.symm phi).property
    · intro hz
      let zC : C := ⟨z, hz⟩
      refine ⟨e zC, ?_⟩
      exact heval zC

/-- The canonical bidual column realization of the split direct sum is
literally the elementary code `K(1,c) \oplus C`. -/
theorem canonicalSplitDirectSumCode_eq_directSumBlockCode_exact
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι)) :
    canonicalSplitDirectSumCode (K := K) c C =
      directSumBlockCode (K := K) c C := by
  let gen := canonicalBlockCodeGenerator (K := K) C
  have hgenRange : LinearMap.range gen = C :=
    (canonicalBlockCodeGenerator_exact C).2
  ext w
  constructor
  · rintro ⟨phi, rfl⟩
    let psi : Module.Dual K (Module.Dual K C) :=
      { toFun := fun theta => phi (0, theta)
        map_add' := by
          intro u v
          rw [show ((0 : K), u + v) = (0, u) + (0, v) by ext <;> simp,
            map_add]
        map_smul' := by
          intro a v
          rw [show ((0 : K), a • v) = a • (0, v) by ext <;> simp,
            map_smul]
          rfl }
    have hz : gen psi ∈ C :=
      hgenRange.le ⟨psi, rfl⟩
    let zC : C := ⟨gen psi, hz⟩
    refine ⟨(phi (1, 0), zC), ?_⟩
    funext o q
    cases o with
    | none =>
      fin_cases q
      · rfl
      · change c * phi (1, 0) = phi (c, 0)
        have hpair : (c, (0 : Module.Dual K C)) =
            c • ((1 : K), (0 : Module.Dual K C)) := by
          ext <;> simp
        rw [hpair, map_smul]
        rfl
    | some i =>
      fin_cases q <;> rfl
  · rintro ⟨az, rfl⟩
    have hz : (az.2 : QaryBlockRow K ι) ∈ LinearMap.range gen :=
      hgenRange.ge az.2.2
    obtain ⟨psi, hpsi⟩ := hz
    let phi : Module.Dual K (K × Module.Dual K C) :=
      { toFun := fun p => az.1 * p.1 + psi p.2
        map_add' := by intro u v; simp; ring
        map_smul' := by intro a v; simp; ring }
    refine ⟨phi, ?_⟩
    funext o q
    cases o with
    | none =>
      fin_cases q
      · simp [blockColumnGenerator, splitDirectSumFirstColumns,
          splitDirectSumSecondColumns, directSumBlockGenerator,
          directSumHeadColumn, directSumCompanionColumn, phi, head2]
      · simp [blockColumnGenerator, splitDirectSumFirstColumns,
          splitDirectSumSecondColumns, directSumBlockGenerator,
          directSumHeadColumn, directSumCompanionColumn, phi, head2]
        ring
    | some i =>
      have hi := congrFun hpsi i
      fin_cases q
      · have hi0 := congrFun hi 0
        simpa [gen, canonicalBlockCodeGenerator, blockColumnGenerator,
          blockCodeFirstCoordinate, phi, splitDirectSumFirstColumns,
          splitDirectSumSecondColumns, liftedParentColumn,
          directSumBlockGenerator, head2] using hi0
      · have hi1 := congrFun hi 1
        simpa [gen, canonicalBlockCodeGenerator, blockColumnGenerator,
          blockCodeSecondCoordinate, phi, splitDirectSumFirstColumns,
          splitDirectSumSecondColumns, liftedParentColumn,
          directSumBlockGenerator, head2] using hi1

/-- Exact conversion from rank-one intersection to corank-one canonical
defect columns. -/
theorem canonicalBlockCode_defect_corank_of_intersection_one_exact
    [Fintype ι] (c : K) (C : Submodule K (QaryBlockRow K ι))
    (hsquare : Module.finrank K C = Fintype.card ι)
    (hone : Module.finrank K
      ↥(C ⊓ qaryIsotropicLineCode (K := K) c) = 1) :
    Module.finrank K
      (span K (range (fun i =>
        blockCodeSecondCoordinate (K := K) C i -
          c • blockCodeFirstCoordinate (K := K) C i))) + 1 =
      Fintype.card ι := by
  obtain ⟨hinjective, hrange⟩ := canonicalBlockCodeGenerator_exact C
  have hrank :=
    blockColumnGenerator_defect_rank_add_intersection_finrank_exact
      c (blockCodeFirstCoordinate (K := K) C)
        (blockCodeSecondCoordinate (K := K) C) hinjective
  rw [show blockColumnGenerator
        (blockCodeFirstCoordinate (K := K) C)
        (blockCodeSecondCoordinate (K := K) C) =
      canonicalBlockCodeGenerator (K := K) C by rfl,
    hrange, hone, Subspace.dual_finrank_eq, hsquare] at hrank
  exact hrank

/-- Exact preservation of rank-one intersection under the cross-paired split
direct-sum branch, stated directly for an arbitrary parent block code. -/
theorem exists_crossPaired_canonicalCode_directSum_intersection_one_exact
    [Fintype ι] [DecidableEq ι]
    (c : K) (C : Submodule K (QaryBlockRow K ι))
    (hc : c ^ 2 = (-1 : K))
    (hsquare : Module.finrank K C = Fintype.card ι)
    (hone : Module.finrank K
      ↥(C ⊓ qaryIsotropicLineCode (K := K) c) = 1) :
    ∃ i : ι,
      let a := blockCodeFirstCoordinate (K := K) C
      let b := blockCodeSecondCoordinate (K := K) C
      let xChild := crossPairedDirectSumFirstColumns (K := K) c a i
      let yChild := crossPairedDirectSumSecondColumns (K := K) a b i
      Module.finrank K
        ↥((LinearMap.range (blockColumnGenerator (K := K) xChild yChild) :
            Submodule K (QaryBlockRow K (Option (Option {j : ι // j ≠ i})))) ⊓
          qaryIsotropicLineCode (K := K) c) = 1 := by
  let a := blockCodeFirstCoordinate (K := K) C
  let b := blockCodeSecondCoordinate (K := K) C
  obtain ⟨hgen, _⟩ := canonicalBlockCodeGenerator_exact C
  have hsquareDual : Module.finrank K (Module.Dual K C) = Fintype.card ι := by
    rw [Subspace.dual_finrank_eq, hsquare]
  have hcorank : Module.finrank K
      (span K (range (fun i => b i - c • a i))) + 1 = Fintype.card ι := by
    simpa [a, b] using
      canonicalBlockCode_defect_corank_of_intersection_one_exact
        c C hsquare hone
  simpa [a, b] using
    exists_crossPaired_directSum_code_intersection_finrank_one_exact
      c a b hc hgen hsquareDual hcorank

/-- The literal cross-paired child generator is the scalar-coordinate
reindexing of the unpaired split direct-sum generator. -/
theorem crossPairedGenerator_eq_scalarCoordinateReindex_exact
    [DecidableEq ι] (c : K) (a b : ι → V) (i : ι) :
    blockColumnGenerator (K := K)
        (crossPairedDirectSumFirstColumns (K := K) c a i)
        (crossPairedDirectSumSecondColumns (K := K) a b i) =
      (scalarCoordinateReindexBlockLinearEquiv (K := K)
        (crossPairScalarEquiv i)).toLinearMap.comp
        (blockColumnGenerator (K := K)
          (splitDirectSumFirstColumns (K := K) a)
          (splitDirectSumSecondColumns (K := K) c b)) := by
  ext phi o q
  cases o with
  | none =>
      fin_cases q <;>
        simp [blockColumnGenerator, crossPairedDirectSumFirstColumns,
          crossPairedDirectSumSecondColumns, splitDirectSumFirstColumns,
          splitDirectSumSecondColumns, scalarCoordinateReindexBlockLinearEquiv,
          crossPairScalarEquiv, directSumCompanionColumn, liftedParentColumn,
          head2]
  | some o =>
      cases o with
      | none =>
          fin_cases q <;>
            simp [blockColumnGenerator, crossPairedDirectSumFirstColumns,
              crossPairedDirectSumSecondColumns, splitDirectSumFirstColumns,
              splitDirectSumSecondColumns,
              scalarCoordinateReindexBlockLinearEquiv, crossPairScalarEquiv,
              directSumHeadColumn, liftedParentColumn, head2]
      | some j =>
          fin_cases q <;>
            simp [blockColumnGenerator, crossPairedDirectSumFirstColumns,
              crossPairedDirectSumSecondColumns, splitDirectSumFirstColumns,
              splitDirectSumSecondColumns,
              scalarCoordinateReindexBlockLinearEquiv, crossPairScalarEquiv,
              liftedParentColumn, head2]

/-- Exact code-level scalar-permutation identity for the cross-paired child. -/
theorem crossPairedCode_eq_scalarCoordinateReindex_exact
    [DecidableEq ι] (c : K) (a b : ι → V) (i : ι) :
    LinearMap.range
        (blockColumnGenerator (K := K)
          (crossPairedDirectSumFirstColumns (K := K) c a i)
          (crossPairedDirectSumSecondColumns (K := K) a b i)) =
      Submodule.map
        (scalarCoordinateReindexBlockLinearEquiv (K := K)
          (crossPairScalarEquiv i)).toLinearMap
        (LinearMap.range
          (blockColumnGenerator (K := K)
            (splitDirectSumFirstColumns (K := K) a)
            (splitDirectSumSecondColumns (K := K) c b))) := by
  rw [crossPairedGenerator_eq_scalarCoordinateReindex_exact c a b i,
    LinearMap.range_comp]

/-- The generic cross-paired code identity, conjugated to an actual
scalar-coordinate permutation of `Fin (n+1) × Fin 2`. -/
theorem finCrossPair_scalarCoordinatePermuted_directSum_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (i : Fin n) :
    scalarCoordinatePermutedBlockCode (K := K)
        (finCrossPairScalarPerm i)
        (finCanonicalSplitDirectSumCode (K := K) c C) =
      relabelBlockCode (K := K)
        (finSuccEquivLast.trans
          (Equiv.optionCongr (Equiv.optionSubtypeNe i).symm))
        (LinearMap.range
          (blockColumnGenerator (K := K)
            (crossPairedDirectSumFirstColumns (K := K) c
              (blockCodeFirstCoordinate (K := K) C) i)
            (crossPairedDirectSumSecondColumns (K := K)
              (blockCodeFirstCoordinate (K := K) C)
              (blockCodeSecondCoordinate (K := K) C) i))) := by
  let directIndex : Fin (n + 1) ≃ Option (Fin n) := finSuccEquivLast
  let childIndex : Fin (n + 1) ≃ Option (Option {j : Fin n // j ≠ i}) :=
    finSuccEquivLast.trans (Equiv.optionCongr (Equiv.optionSubtypeNe i).symm)
  let directGen := blockColumnGenerator (K := K)
    (splitDirectSumFirstColumns (K := K)
      (blockCodeFirstCoordinate (K := K) C))
    (splitDirectSumSecondColumns (K := K) c
      (blockCodeSecondCoordinate (K := K) C))
  let crossGen := blockColumnGenerator (K := K)
    (crossPairedDirectSumFirstColumns (K := K) c
      (blockCodeFirstCoordinate (K := K) C) i)
    (crossPairedDirectSumSecondColumns (K := K)
      (blockCodeFirstCoordinate (K := K) C)
      (blockCodeSecondCoordinate (K := K) C) i)
  let P := scalarCoordinatePermuteBlockLinearEquiv (K := K)
    (finCrossPairScalarPerm i)
  let LD := blockRelabelLinearEquiv (K := K) directIndex
  let LC := blockRelabelLinearEquiv (K := K) childIndex
  let X := scalarCoordinateReindexBlockLinearEquiv (K := K)
    (crossPairScalarEquiv i)
  have hcross : LinearMap.range crossGen =
      Submodule.map X.toLinearMap (LinearMap.range directGen) := by
    simpa [crossGen, directGen, X] using
      crossPairedCode_eq_scalarCoordinateReindex_exact
        c (blockCodeFirstCoordinate (K := K) C)
          (blockCodeSecondCoordinate (K := K) C) i
  have hlinear : P.toLinearMap.comp LD.toLinearMap =
      LC.toLinearMap.comp X.toLinearMap := by
    ext v j q
    simp [P, LD, LC, X, directIndex, childIndex,
      scalarCoordinatePermuteBlockLinearEquiv,
      blockRelabelLinearEquiv, scalarCoordinateReindexBlockLinearEquiv,
      finCrossPairScalarPerm]
  change Submodule.map P.toLinearMap
      (Submodule.map LD.toLinearMap (LinearMap.range directGen)) =
    Submodule.map LC.toLinearMap (LinearMap.range crossGen)
  rw [hcross, ← Submodule.map_comp, ← Submodule.map_comp, hlinear]

/-- Exact `Fin (n+1) × Fin 2` direct-sum induction step.

If the parent code has a rank-one intersection in its present oriented
pairing, then its canonical split direct sum admits an explicit scalar
coordinate permutation with rank-one intersection. -/
theorem finCanonicalSplitDirectSum_has_rankOne_orientedPairing_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (hc : c ^ 2 = (-1 : K))
    (hsquare : Module.finrank K C = n)
    (hone : Module.finrank K
      ↥(C ⊓ qaryIsotropicLineCode (K := K) c) = 1) :
    HasQaryRankOneOrientedPairing c
      (finCanonicalSplitDirectSumCode (K := K) c C) := by
  obtain ⟨i, hi⟩ :=
    exists_crossPaired_canonicalCode_directSum_intersection_one_exact
      c C hc (by simpa using hsquare) hone
  refine ⟨finCrossPairScalarPerm i, ?_⟩
  rw [finCrossPair_scalarCoordinatePermuted_directSum_exact c C i]
  let childIndex : Fin (n + 1) ≃
      Option (Option {j : Fin n // j ≠ i}) :=
    finSuccEquivLast.trans (Equiv.optionCongr (Equiv.optionSubtypeNe i).symm)
  let childCode : Submodule K
      (QaryBlockRow K (Option (Option {j : Fin n // j ≠ i}))) :=
    LinearMap.range
      (blockColumnGenerator (K := K)
        (crossPairedDirectSumFirstColumns (K := K) c
          (blockCodeFirstCoordinate (K := K) C) i)
        (crossPairedDirectSumSecondColumns (K := K)
          (blockCodeFirstCoordinate (K := K) C)
          (blockCodeSecondCoordinate (K := K) C) i))
  have hrelabel :=
    finrank_relabelBlockCode_inf_qaryIsotropicLineCode_exact
      (K := K) c childIndex childCode
  rw [hrelabel]
  simpa [childCode] using hi

/-- Exact direct-sum induction theorem for the scalar branch produced by
`directSumRows`.  Its `K(1,-c)` summand is first corrected by the explicit
new-coordinate swap and is then handled by the canonical direct-sum theorem. -/
theorem finDirectSumBlockCode_neg_has_rankOne_orientedPairing_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (hc : c ^ 2 = (-1 : K))
    (hsquare : Module.finrank K C = n)
    (hone : Module.finrank K
      ↥(C ⊓ qaryIsotropicLineCode (K := K) c) = 1) :
    HasQaryRankOneOrientedPairing c
      (finDirectSumBlockCode (K := K) (-c) C) := by
  have hcode : finCanonicalSplitDirectSumCode (K := K) c C =
      finDirectSumBlockCode (K := K) c C := by
    unfold finCanonicalSplitDirectSumCode finDirectSumBlockCode
    rw [canonicalSplitDirectSumCode_eq_directSumBlockCode_exact]
  have hcanonical :=
    finCanonicalSplitDirectSum_has_rankOne_orientedPairing_exact
      c C hc hsquare hone
  rw [hcode] at hcanonical
  apply (hasQaryRankOneOrientedPairing_scalarCoordinatePermuted_iff
    c finLastBlockScalarSwap
      (finDirectSumBlockCode (K := K) (-c) C)).mp
  rw [finLastSwap_directSumBlockCode_neg_exact c C hc]
  exact hcanonical

/-- Permutation-free direct-sum induction step.  A parent oriented pairing is
transported across the child by `finExtendOldScalarPerm`, after which the
fixed-pairing direct-sum theorem applies. -/
theorem finDirectSumBlockCode_neg_has_rankOne_orientedPairing_of_parent_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (hc : c ^ 2 = (-1 : K))
    (hsquare : Module.finrank K C = n)
    (hparent : HasQaryRankOneOrientedPairing c C) :
    HasQaryRankOneOrientedPairing c
      (finDirectSumBlockCode (K := K) (-c) C) := by
  obtain ⟨σ, hone⟩ := hparent
  have hsquare' : Module.finrank K
      (scalarCoordinatePermutedBlockCode (K := K) σ C) = n := by
    unfold scalarCoordinatePermutedBlockCode
    rw [(scalarCoordinatePermuteBlockLinearEquiv (K := K) σ).finrank_map_eq]
    exact hsquare
  have hfixed :=
    finDirectSumBlockCode_neg_has_rankOne_orientedPairing_exact
      c (scalarCoordinatePermutedBlockCode (K := K) σ C)
        hc hsquare' hone
  rw [← finExtendOld_directSumBlockCode_exact (-c) σ C] at hfixed
  exact (hasQaryRankOneOrientedPairing_scalarCoordinatePermuted_iff
    c (finExtendOldScalarPerm σ)
      (finDirectSumBlockCode (K := K) (-c) C)).mp hfixed

/-- Permutation-free literal building-up induction step.  The parent pairing,
the correction word, and the dual functional are transported together before
the fixed-pairing theorem is applied. -/
theorem finBuildingUpBlockCode_has_rankOne_orientedPairing_of_parent_exact
    {n : ℕ} (c : K) (C : Submodule K (QaryBlockRow K (Fin n)))
    (x : QaryBlockRow K (Fin n)) (ell : Module.Dual K C)
    (hc0 : c ≠ 0)
    (hparent : HasQaryRankOneOrientedPairing c C) :
    HasQaryRankOneOrientedPairing c
      (finBuildingUpBlockCode (K := K) c C x ell) := by
  obtain ⟨σ, hone⟩ := hparent
  let P := scalarCoordinatePermuteBlockLinearEquiv (K := K) σ
  let C' := scalarCoordinatePermutedBlockCode (K := K) σ C
  let E : C ≃ₗ[K] C' := P.submoduleMap C
  have hfixed := finBuildingUpBlockCode_has_rankOne_orientedPairing_exact
    c C' (P x) (ell.comp E.symm.toLinearMap) hc0 hone
  have hnat := finExtendOld_buildingUpBlockCode_exact
    (K := K) c σ C x ell
  dsimp only at hnat
  rw [← hnat] at hfixed
  exact (hasQaryRankOneOrientedPairing_scalarCoordinatePermuted_iff
    c (finExtendOldScalarPerm σ)
      (finBuildingUpBlockCode (K := K) c C x ell)).mp hfixed

/-- Every nonempty product of the standard isotropic line has an oriented
pairing whose intersection with the standard product has dimension one. -/
theorem qaryIsotropicLineCode_has_rankOne_orientedPairing_exact
    {n : ℕ} (hn : 0 < n) (c : K) (hc : c ^ 2 = (-1 : K)) :
    HasQaryRankOneOrientedPairing c
      (qaryIsotropicLineCode (K := K) (ι := Fin n) c) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      refine ⟨Equiv.refl (Fin 1 × Fin 2), ?_⟩
      rw [scalarCoordinatePermutedBlockCode_refl_exact, inf_idem]
      simpa using finrank_qaryIsotropicLineCode_exact
        (K := K) (ι := Fin 1) c
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hparent := ih hnpos
      have hsquare : Module.finrank K
          ↥(qaryIsotropicLineCode (K := K) (ι := Fin n) c) = n := by
        simpa using finrank_qaryIsotropicLineCode_exact
          (K := K) (ι := Fin n) c
      have hneg :=
        finDirectSumBlockCode_neg_has_rankOne_orientedPairing_of_parent_exact
          c (qaryIsotropicLineCode (K := K) (ι := Fin n) c)
            hc hsquare hparent
      have hpermuted : HasQaryRankOneOrientedPairing c
          (scalarCoordinatePermutedBlockCode (K := K)
            finLastBlockScalarSwap
            (finDirectSumBlockCode (K := K) (-c)
              (qaryIsotropicLineCode (K := K) (ι := Fin n) c))) :=
        (hasQaryRankOneOrientedPairing_scalarCoordinatePermuted_iff
          c finLastBlockScalarSwap
            (finDirectSumBlockCode (K := K) (-c)
              (qaryIsotropicLineCode (K := K) (ι := Fin n) c))).mpr hneg
      rw [finLastSwap_directSumBlockCode_neg_exact c _ hc,
        finDirectSumBlockCode_qaryIsotropicLineCode_exact] at hpermuted
      exact hpermuted

end BuildingUpFormalization.Components.QaryRankOnePairingMerge
