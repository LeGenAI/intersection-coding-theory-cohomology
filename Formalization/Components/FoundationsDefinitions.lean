import Formalization.Archive.SubmittedBaseline

set_option autoImplicit false

namespace BuildingUpFormalization.Components.Foundations

section PlaneForms

variable {K : Type*} [Field K]

abbrev Plane (K : Type*) := Fin 2 → K

def planeE0 : Plane K := Pi.single 0 1

def planeE1 : Plane K := Pi.single 1 1

/-- The ordinary coding-theoretic Euclidean form on two coordinates. -/
def standardEuclideanPlaneForm : LinearMap.BilinForm K (Plane K) :=
  dotBilin (K := K) (n := 2)

/-- The alternating hyperbolic form with Gram matrix `!![0, 1; 1, 0]`. -/
def alternatingHyperbolicPlaneForm : LinearMap.BilinForm K (Plane K) :=
  LinearMap.mk₂ K
    (fun u v => u 0 * v 1 + u 1 * v 0)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)

/-- A linear equivalence preserving two explicitly named bilinear forms. -/
def IsFormIsometry
    {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (Bᵥ : LinearMap.BilinForm K V) (B𝓌 : LinearMap.BilinForm K W)
    (e : V ≃ₗ[K] W) : Prop :=
  ∀ x y, B𝓌 (e x) (e y) = Bᵥ x y

end PlaneForms

section LagrangianDefinitions

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Total isotropy stated as the exact submodule inclusion it means. -/
def IsTotallyIsotropic
    (B : LinearMap.BilinForm K V) (L : Submodule K V) : Prop :=
  L ≤ B.orthogonal L

/-- Maximality among totally isotropic submodules, ordered by inclusion. -/
def IsMaximalTotallyIsotropic
    (B : LinearMap.BilinForm K V) (L : Submodule K V) : Prop :=
  IsTotallyIsotropic B L ∧
    ∀ M : Submodule K V, IsTotallyIsotropic B M → L ≤ M → M = L

/-- The self-orthogonal notion used by the paper-facing Lean definitions. -/
def IsSelfOrthogonal
    (B : LinearMap.BilinForm K V) (L : Submodule K V) : Prop :=
  L = B.orthogonal L

end LagrangianDefinitions

section SystematicForm

variable {K : Type*} [Field K]

/-- The row family of the systematic generator matrix `[I_k | A]`. -/
def systematicRows {k : ℕ} (A : Matrix (Fin k) (Fin k) K) :
    Fin k → Fin (k + k) → K :=
  fun i => Fin.append (Pi.single i 1) (A i)

end SystematicForm

end BuildingUpFormalization.Components.Foundations
