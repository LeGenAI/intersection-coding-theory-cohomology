import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Prod
import Formalization.Components.QaryRankBoxedNormalizationDefinitions
import Formalization.Components.QaryRankOneOrientedPairingDefinitions

set_option autoImplicit false

namespace BuildingUpFormalization.Components.QaryRankOnePairingMerge

open BuildingUpFormalization.Components.QaryRankBoxedNormalization
open BuildingUpFormalization.Components.SplitBoxed

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Coefficients of the standard product of isotropic lines.  Evaluation at
the first scalar coordinate is the inverse map. -/
def qaryIsotropicLineCodeLinearEquiv (c : K) :
    (ι → K) ≃ₗ[K] ↥(qaryIsotropicLineCode (K := K) (ι := ι) c) where
  toFun a := ⟨fun i => head2 (a i) (c * a i), by
    change qaryBlockDefectLinear (K := K) c
      (fun i => head2 (a i) (c * a i)) = 0
    funext i
    simp [qaryBlockDefectLinear, blockDefectLinear, blockDefect, head2]⟩
  invFun z := fun i => z.1 i 0
  left_inv a := by
    funext i
    rfl
  right_inv z := by
    apply Subtype.ext
    funext i q
    fin_cases q
    · rfl
    · have hi := congrFun z.2 i
      change z.1 i 1 - c * z.1 i 0 = 0 at hi
      exact (sub_eq_zero.mp hi).symm
  map_add' a b := by
    apply Subtype.ext
    funext i q
    fin_cases q <;> simp [head2, mul_add]
  map_smul' a b := by
    apply Subtype.ext
    funext i q
    fin_cases q
    · simp [head2]
    · simp [head2]
      ring

/-- Embed a parent defect column into the child defect space. -/
def liftedDefect (v : V) : K × V := (0, v)

/-- The first defect column created by cross-pairing the new split block
with one selected parent block. -/
def firstCrossDefect (c : K) (a : V) : K × V := (-c, a)

/-- The second defect column created by the same cross-pairing. -/
def secondCrossDefect (b : V) : K × V := (1, b)

/-- A basis-sized subfamily: the lifted independent parent columns together
with the first cross-pair defect column. -/
def crossPairBasis (c : K) (d : ι → V) (a : V) : Option ι → K × V
  | none => firstCrossDefect c a
  | some i => liftedDefect (d i)

/-- The complete child defect family.  It contains two cross-pair columns
and all lifted independent parent columns. -/
def crossPairDefects (c : K) (d : ι → V) (a b : V) : Option (Option ι) → K × V
  | none => secondCrossDefect b
  | some j => crossPairBasis c d a j

/-- A parent defect family with one selected column distinguished as `none`.
The selected column will be eliminated from a relation whose coefficient at
`none` is nonzero. -/
def parentDefectFamily (d : ι → V) (e : V) : Option ι → V
  | none => e
  | some i => d i

/-- Defect of a two-coordinate block of generator columns. -/
def generatorColumnPairDefect (c : K) (x y : K × V) : K × V :=
  y - c • x

/-- First new generator column of the direct summand `K(1,c)`. -/
def directSumHeadColumn : K × V := (1, 0)

/-- Second new generator column of the direct summand `K(1,c)`. -/
def directSumCompanionColumn (c : K) : K × V := (c, 0)

/-- A parent generator column embedded below the new direct-summand row. -/
def liftedParentColumn (v : V) : K × V := (0, v)

/-- Literal defect family obtained by cross-pairing the two new coordinates
of `K(1,c)` with one selected parent coordinate pair. -/
def crossPairedDirectSumDefects (c : K) (d : ι → V) (a b : V) :
    Option (Option ι) → K × V
  | none => generatorColumnPairDefect c
      (directSumCompanionColumn c) (liftedParentColumn b)
  | some none => generatorColumnPairDefect c
      directSumHeadColumn (liftedParentColumn a)
  | some (some i) => liftedDefect (d i)

/-- The dual evaluation map of a finite column family.  A functional on the
column space is sent to its values on every column.  Equivalently, this is
the transpose of the linear-combination map of the family. -/
def columnEvaluationDual [Fintype ι] (v : ι → V) :
    Module.Dual K V →ₗ[K] Module.Dual K (ι → K) :=
  (Fintype.linearCombination K v).dualMap

/-- Evaluation of a dual coefficient vector on every member of a column
family. -/
def columnEvaluation (v : ι → V) :
    Module.Dual K V →ₗ[K] (ι → K) where
  toFun phi i := phi (v i)
  map_add' phi psi := by rfl
  map_smul' a phi := by rfl

/-- Generator map determined by the first and second scalar columns of each
two-coordinate block.  Its domain is the dual coefficient space, so evaluation
against a column is canonical and does not choose a basis. -/
def blockColumnGenerator (x y : ι → V) :
    Module.Dual K V →ₗ[K] QaryBlockRow K ι where
  toFun phi i := head2 (phi (x i)) (phi (y i))
  map_add' phi psi := by
    funext i j
    fin_cases j <;> rfl
  map_smul' a phi := by
    funext i j
    fin_cases j <;> rfl

/-- First scalar columns after cross-pairing a new split summand with the
selected parent block `i`. -/
def crossPairedDirectSumFirstColumns
    (c : K) (a : ι → V) (i : ι) :
    Option (Option {j : ι // j ≠ i}) → K × V
  | none => directSumCompanionColumn c
  | some none => directSumHeadColumn
  | some (some j) => liftedParentColumn (a j)

/-- Second scalar columns after the same cross-pairing. -/
def crossPairedDirectSumSecondColumns
    (a b : ι → V) (i : ι) :
    Option (Option {j : ι // j ≠ i}) → K × V
  | none => liftedParentColumn (b i)
  | some none => liftedParentColumn (a i)
  | some (some j) => liftedParentColumn (b j)

/-- First scalar-coordinate functional of block `i`, restricted to a block
code `C`. -/
def blockCodeFirstCoordinate
    (C : Submodule K (QaryBlockRow K ι)) (i : ι) : Module.Dual K C where
  toFun z := (z : QaryBlockRow K ι) i 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Second scalar-coordinate functional of block `i`, restricted to `C`. -/
def blockCodeSecondCoordinate
    (C : Submodule K (QaryBlockRow K ι)) (i : ι) : Module.Dual K C where
  toFun z := (z : QaryBlockRow K ι) i 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical bidual generator of a block code, obtained from its restricted
coordinate functionals. -/
def canonicalBlockCodeGenerator
    (C : Submodule K (QaryBlockRow K ι)) :
    Module.Dual K (Module.Dual K C) →ₗ[K] QaryBlockRow K ι :=
  blockColumnGenerator
    (blockCodeFirstCoordinate (K := K) C)
    (blockCodeSecondCoordinate (K := K) C)

/-- First scalar columns of the unpaired split direct sum `K(1,c) ⊕ C`. -/
def splitDirectSumFirstColumns (a : ι → V) : Option ι → K × V
  | none => directSumHeadColumn
  | some j => liftedParentColumn (a j)

/-- Second scalar columns of the unpaired split direct sum. -/
def splitDirectSumSecondColumns (c : K) (b : ι → V) : Option ι → K × V
  | none => directSumCompanionColumn c
  | some j => liftedParentColumn (b j)

/-- Reindex scalar coordinates while allowing the source and target block
index types to differ. -/
def scalarCoordinateReindexBlockLinearEquiv {κ : Type*}
    (σ : κ × Fin 2 ≃ ι × Fin 2) :
    QaryBlockRow K ι ≃ₗ[K] QaryBlockRow K κ where
  toFun v k q := v (σ (k, q)).1 (σ (k, q)).2
  invFun w i q := w (σ.symm (i, q)).1 (σ.symm (i, q)).2
  left_inv v := by
    funext i q
    simp
  right_inv w := by
    funext k q
    simp
  map_add' u v := rfl
  map_smul' a v := rfl

/-- The scalar-coordinate permutation which cross-pairs the two coordinates
of the new split block with the selected parent block `i`. -/
def crossPairScalarEquiv [DecidableEq ι] (i : ι) :
    Option (Option {j : ι // j ≠ i}) × Fin 2 ≃ Option ι × Fin 2 where
  toFun
    | (none, q) =>
        if q = 0 then (none, 1) else (some i, 1)
    | (some none, q) =>
        if q = 0 then (none, 0) else (some i, 0)
    | (some (some j), q) => (some j, q)
  invFun
    | (none, q) =>
        if q = 0 then (some none, 0) else (none, 0)
    | (some j, q) =>
        if hji : j = i then
          if q = 0 then (some none, 1) else (none, 1)
        else (some (some ⟨j, hji⟩), q)
  left_inv z := by
    rcases z with ⟨o, q⟩
    cases o with
    | none => fin_cases q <;> simp
    | some o =>
        cases o with
        | none => fin_cases q <;> simp
        | some j => fin_cases q <;> simp [j.property]
  right_inv z := by
    rcases z with ⟨o, q⟩
    cases o with
    | none => fin_cases q <;> simp
    | some j =>
        by_cases hji : j = i
        · subst j
          fin_cases q <;> simp
        · fin_cases q <;> simp [hji]

/-- The split direct sum `K(1,c) \oplus C`, using the canonical bidual
generator of `C`. -/
def canonicalSplitDirectSumCode (c : K)
    (C : Submodule K (QaryBlockRow K ι)) :
    Submodule K (QaryBlockRow K (Option ι)) :=
  LinearMap.range
    (blockColumnGenerator (K := K)
      (splitDirectSumFirstColumns (K := K)
        (blockCodeFirstCoordinate (K := K) C))
      (splitDirectSumSecondColumns (K := K) c
        (blockCodeSecondCoordinate (K := K) C)))

/-- The standard `Fin (n+1)` indexing of the split direct sum
`K(1,c) \oplus C`, using the canonical bidual generator of `C`. -/
def finCanonicalSplitDirectSumCode {n : ℕ} (c : K)
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    Submodule K (QaryBlockRow K (Fin (n + 1))) :=
  relabelBlockCode (K := K) finSuccEquivLast
    (canonicalSplitDirectSumCode (K := K) c C)

/-- The explicit scalar-coordinate permutation on `Fin (n+1) × Fin 2`
obtained by conjugating the generic cross-pairing through the standard finite
indexings of the direct-sum and cross-paired block sets. -/
def finCrossPairScalarPerm {n : ℕ} (i : Fin n) :
    Equiv.Perm (Fin (n + 1) × Fin 2) :=
  let directIndex : Fin (n + 1) ≃ Option (Fin n) := finSuccEquivLast
  let childIndex : Fin (n + 1) ≃ Option (Option {j : Fin n // j ≠ i}) :=
    finSuccEquivLast.trans (Equiv.optionCongr (Equiv.optionSubtypeNe i).symm)
  (directIndex.prodCongr (Equiv.refl (Fin 2))).trans
    ((crossPairScalarEquiv i).symm.trans
      (childIndex.symm.prodCongr (Equiv.refl (Fin 2))))

/-- Block form of a Kim--Lee extension.  The functional `ell` records the
Kim--Lee coefficients; the new block of `(a,z)` is
`(a-ell(z), -c ell(z))`, and every old block is copied literally. -/
def kimLeeBlockGenerator [Fintype ι]
    (c : K) (C : Submodule K (QaryBlockRow K ι))
    (ell : Module.Dual K C) :
    K × C →ₗ[K] QaryBlockRow K (Option ι) where
  toFun az
    | none => head2 (az.1 - ell az.2) (-c * ell az.2)
    | some i => (az.2 : QaryBlockRow K ι) i
  map_add' u v := by
    funext o q
    cases o with
    | none => fin_cases q <;> simp [head2] <;> ring
    | some i => rfl
  map_smul' a v := by
    funext o q
    cases o with
    | none => fin_cases q <;> simp [head2] <;> ring
    | some i => rfl

/-- The code generated by the block Kim--Lee extension. -/
def kimLeeBlockCode [Fintype ι]
    (c : K) (C : Submodule K (QaryBlockRow K ι))
    (ell : Module.Dual K C) :
    Submodule K (QaryBlockRow K (Option ι)) :=
  LinearMap.range (kimLeeBlockGenerator (K := K) c C ell)

/-- Standard `Fin (n+1)` indexing of the block Kim--Lee extension. -/
def finKimLeeBlockCode {n : ℕ} (c : K)
    (C : Submodule K (QaryBlockRow K (Fin n)))
    (ell : Module.Dual K C) :
    Submodule K (QaryBlockRow K (Fin (n + 1))) :=
  relabelBlockCode (K := K) finSuccEquivLast
    (kimLeeBlockCode (K := K) c C ell)

/-- The actual block form of the standard building-up generator.  In contrast
to `kimLeeBlockGenerator`, the old coordinates contain the indispensable
term `a • x`: a general generated word has old tail `a x + z`. -/
def buildingUpBlockGenerator [Fintype ι]
    (c : K) (C : Submodule K (QaryBlockRow K ι))
    (x : QaryBlockRow K ι) (ell : Module.Dual K C) :
    K × C →ₗ[K] QaryBlockRow K (Option ι) where
  toFun az
    | none => head2 (az.1 - ell az.2) (-c * ell az.2)
    | some i => az.1 • x i + (az.2 : QaryBlockRow K ι) i
  map_add' u v := by
    funext o q
    cases o with
    | none => fin_cases q <;> simp [head2] <;> ring
    | some i => simp [add_smul, add_assoc, add_left_comm]
  map_smul' a v := by
    funext o q
    cases o with
    | none => fin_cases q <;> simp [head2] <;> ring
    | some i => simp [mul_smul]; ring

/-- The code generated by the literal block form of `buildRows`. -/
def buildingUpBlockCode [Fintype ι]
    (c : K) (C : Submodule K (QaryBlockRow K ι))
    (x : QaryBlockRow K ι) (ell : Module.Dual K C) :
    Submodule K (QaryBlockRow K (Option ι)) :=
  LinearMap.range (buildingUpBlockGenerator (K := K) c C x ell)

/-- Standard finite indexing of the literal block building-up code. -/
def finBuildingUpBlockCode {n : ℕ} (c : K)
    (C : Submodule K (QaryBlockRow K (Fin n)))
    (x : QaryBlockRow K (Fin n)) (ell : Module.Dual K C) :
    Submodule K (QaryBlockRow K (Fin (n + 1))) :=
  relabelBlockCode (K := K) finSuccEquivLast
    (buildingUpBlockCode (K := K) c C x ell)

/-- Group a scalar vector whose coordinates are listed pairwise into finite
two-coordinate blocks. -/
def finScalarBlockLinearEquiv {n : ℕ} :
    (Fin (n * 2) → K) ≃ₗ[K] QaryBlockRow K (Fin n) where
  toFun v i q := v (finProdFinEquiv (i, q))
  invFun R j := R (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm j).2
  left_inv v := by
    funext j
    simpa [finProdFinEquiv_symm_apply] using
      congrArg v (Equiv.apply_symm_apply finProdFinEquiv j)
  right_inv R := by
    funext i q
    simpa [finProdFinEquiv_symm_apply] using congrArg
      (fun p : Fin n × Fin 2 => R p.1 p.2)
      (Equiv.symm_apply_apply finProdFinEquiv (i, q))
  map_add' u v := rfl
  map_smul' a v := rfl

/-- Group the first two scalar coordinates into a new block and the remaining
pairwise scalar coordinates into the old finite blocks. -/
def prependedScalarBlockLinearEquiv {n : ℕ} :
    (Fin (2 + n * 2) → K) ≃ₗ[K] QaryBlockRow K (Option (Fin n)) where
  toFun v
    | none => fun q => v (Fin.castAdd (n * 2) q)
    | some i => fun q => v (Fin.natAdd 2 (finProdFinEquiv (i, q)))
  invFun R := Fin.append (R none)
    (fun j => R (some (finProdFinEquiv.symm j).1)
      (finProdFinEquiv.symm j).2)
  left_inv v := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro q
      simp
    · intro t
      simp only [Fin.append_right]
      simpa [finProdFinEquiv_symm_apply] using congrArg
        (fun s : Fin (n * 2) => v (Fin.natAdd 2 s))
        (Equiv.apply_symm_apply finProdFinEquiv t)
  right_inv R := by
    funext o q
    cases o with
    | none => simp
    | some i =>
      simp only [Fin.append_right]
      simpa [finProdFinEquiv_symm_apply] using congrArg
        (fun p : Fin n × Fin 2 => R (some p.1) p.2)
        (Equiv.symm_apply_apply finProdFinEquiv (i, q))
  map_add' u v := by funext o q; cases o <;> rfl
  map_smul' a v := by funext o q; cases o <;> rfl

/-- A scalar row space read in consecutive two-coordinate blocks. -/
def scalarRowSpaceAsBlock {m n : ℕ}
    (G : Matrix (Fin m) (Fin (n * 2)) K) :
    Submodule K (QaryBlockRow K (Fin n)) :=
  Submodule.map (finScalarBlockLinearEquiv (K := K)).toLinearMap (rowSpace G)

/-- A scalar child row space with its first two coordinates read as the new
block. -/
def prependedScalarRowSpaceAsBlock {m n : ℕ}
    (B : Matrix (Fin m) (Fin (2 + n * 2)) K) :
    Submodule K (QaryBlockRow K (Option (Fin n))) :=
  Submodule.map (prependedScalarBlockLinearEquiv (K := K)).toLinearMap
    (rowSpace B)

/-- The linear functional `z ↦ x · z` after ungrouping a block word into its
consecutive scalar coordinates. -/
def blockDotFunctional {n : ℕ} (x : Fin (n * 2) → K)
    (C : Submodule K (QaryBlockRow K (Fin n))) : Module.Dual K C where
  toFun z := dot x ((finScalarBlockLinearEquiv (K := K)).symm z.1)
  map_add' u v := by
    simp [dot_add_right]
  map_smul' a v := by
    simp [dot_smul_right]

/-- Literal block generator of `K(1,d) \oplus C`. -/
def directSumBlockGenerator (d : K)
    (C : Submodule K (QaryBlockRow K ι)) :
    K × C →ₗ[K] QaryBlockRow K (Option ι) where
  toFun az
    | none => head2 az.1 (d * az.1)
    | some i => (az.2 : QaryBlockRow K ι) i
  map_add' u v := by
    funext o q
    cases o with
    | none => fin_cases q <;> simp [head2, mul_add]
    | some i => rfl
  map_smul' a v := by
    funext o q
    cases o with
    | none =>
      fin_cases q
      · simp [head2]
      · simp [head2]
        ring
    | some i => rfl

/-- Literal block code `K(1,d) \oplus C`. -/
def directSumBlockCode (d : K)
    (C : Submodule K (QaryBlockRow K ι)) :
    Submodule K (QaryBlockRow K (Option ι)) :=
  LinearMap.range (directSumBlockGenerator (K := K) d C)

/-- Swap the two scalar coordinates of the distinguished `none` block and
fix every old block. -/
def headBlockScalarSwap : Equiv.Perm (Option ι × Fin 2) where
  toFun
    | (none, q) => (none, Equiv.swap (0 : Fin 2) 1 q)
    | (some i, q) => (some i, q)
  invFun
    | (none, q) => (none, Equiv.swap (0 : Fin 2) 1 q)
    | (some i, q) => (some i, q)
  left_inv z := by
    rcases z with ⟨o, q⟩
    cases o with
    | none => fin_cases q <;> simp
    | some i => rfl
  right_inv z := by
    rcases z with ⟨o, q⟩
    cases o with
    | none => fin_cases q <;> simp
    | some i => rfl

/-- Conjugate the distinguished-block swap to the standard
`Fin (n+1) × Fin 2` indexing. -/
def finLastBlockScalarSwap {n : ℕ} : Equiv.Perm (Fin (n + 1) × Fin 2) :=
  let index := finSuccEquivLast.prodCongr (Equiv.refl (Fin 2))
  index.trans ((headBlockScalarSwap (ι := Fin n)).trans index.symm)

/-- Extend a scalar-coordinate permutation of the parent across a new
distinguished block.  The two scalar coordinates of `none` are fixed, while
the old scalar coordinates are permuted exactly by `σ`. -/
def optionHeadFixedScalarPerm {n : ℕ}
    (σ : Equiv.Perm (Fin n × Fin 2)) :
    Equiv.Perm (Option (Fin n) × Fin 2) where
  toFun
    | (none, q) => (none, q)
    | (some i, q) => (some (σ (i, q)).1, (σ (i, q)).2)
  invFun
    | (none, q) => (none, q)
    | (some i, q) => (some (σ.symm (i, q)).1, (σ.symm (i, q)).2)
  left_inv z := by
    rcases z with ⟨o, q⟩
    cases o with
    | none => rfl
    | some i => simp
  right_inv z := by
    rcases z with ⟨o, q⟩
    cases o with
    | none => rfl
    | some i => simp

/-- Conjugate `optionHeadFixedScalarPerm` to the standard child indexing.
Thus the last block introduced by `finSuccEquivLast` is fixed and `σ` acts on
all old scalar coordinates. -/
def finExtendOldScalarPerm {n : ℕ}
    (σ : Equiv.Perm (Fin n × Fin 2)) :
    Equiv.Perm (Fin (n + 1) × Fin 2) :=
  let index := finSuccEquivLast.prodCongr (Equiv.refl (Fin 2))
  index.trans ((optionHeadFixedScalarPerm σ).trans index.symm)

/-- Scalar-coordinate permutation induced by a permutation of whole finite
blocks.  The inverse is used so that its action agrees with
`relabelBlockCode σ`. -/
def blockRelabelScalarPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n × Fin 2) :=
  σ.symm.prodCongr (Equiv.refl (Fin 2))

/-- Standard finite indexing of the literal direct-sum block code. -/
def finDirectSumBlockCode {n : ℕ} (d : K)
    (C : Submodule K (QaryBlockRow K (Fin n))) :
    Submodule K (QaryBlockRow K (Fin (n + 1))) :=
  relabelBlockCode (K := K) finSuccEquivLast
    (directSumBlockCode (K := K) d C)

end BuildingUpFormalization.Components.QaryRankOnePairingMerge
