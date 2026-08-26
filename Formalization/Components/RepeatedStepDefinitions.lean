import Formalization.Components.Foundations

set_option autoImplicit false

namespace BuildingUpFormalization.Components.RepeatedStep

variable {K : Type*} [Field K]

/-- One pivot and its two-coordinate column, with the parent left literal. -/
def borderedRows {m n : ℕ} (c p : K) (rho : Fin n → K)
    (gamma : Fin m → K) (G : Matrix (Fin m) (Fin n) K) :
    Matrix (Fin (m + 1)) (Fin (2 + n)) K :=
  Fin.cons (prepend2 p (c * p + 1) rho)
    (fun i => prepend2 (gamma i) (c * gamma i) (G i))

/-- Invertible top-row operation when a is nonzero; all lower rows are fixed. -/
def topRowOperation {m n : ℕ} (a : K) (z : Fin m → K)
    (B : Matrix (Fin (m + 1)) (Fin n) K) : Matrix (Fin (m + 1)) (Fin n) K :=
  Fin.cons (a • B 0 + ∑ i, z i • B i.succ) (fun i => B i.succ)

def normalizingCoeff {m : ℕ} (c p : K) (gamma : Fin m → K) (s : Fin m) : K :=
  (c - p) / gamma s

def normalizedTail {m n : ℕ} (c p : K) (rho : Fin n → K)
    (gamma : Fin m → K) (G : Matrix (Fin m) (Fin n) K) (s : Fin m) : Fin n → K :=
  c⁻¹ • (rho + normalizingCoeff c p gamma s • G s)

def normalizedBorder {m n : ℕ} (c p : K) (rho : Fin n → K)
    (gamma : Fin m → K) (G : Matrix (Fin m) (Fin n) K) (s : Fin m) :=
  topRowOperation c⁻¹ (Pi.single s (c⁻¹ * normalizingCoeff c p gamma s))
    (borderedRows c p rho gamma G)

/-- Generator of K(1,-c) direct-sum the literal parent code. -/
def directSumRows {m n : ℕ} (c : K) (G : Matrix (Fin m) (Fin n) K) :
    Matrix (Fin (m + 1)) (Fin (2 + n)) K :=
  Fin.cons (prepend2 1 (-c) 0) (fun i => prepend2 0 0 (G i))

end BuildingUpFormalization.Components.RepeatedStep
