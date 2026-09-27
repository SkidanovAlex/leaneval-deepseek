import Mathlib

/-!
# Auxiliary definitions for `LinAlgMatrixIneq`

We need the sharp inequality

`∏ i, Real.sqrt (λ i) / (1 - λ i) ≤ (Real.sqrt n / (n - 1)) ^ n`

for `λ : Fin n → ℝ`, `0 ≤ λ i`, `λ i < 1`, `∑ i, λ i = 1`, `n ≥ 3`.

The proof uses a maximum argument.  This file collects the basic objects:
`matG` (the logarithm of the summand), `matPhi` (its derivative), `matF` (the
quantity to bound), `matC` (the claimed sharp constant) and the compact box
`Kset`.
-/

namespace Work.Mostow

noncomputable section

/-- `log (√x / (1 - x))`. -/
def matG (x : ℝ) : ℝ := (1 / 2 : ℝ) * Real.log x - Real.log (1 - x)

/-- The derivative of `matG`: `1/(2x) + 1/(1-x)`. -/
def matPhi (x : ℝ) : ℝ := 1 / (2 * x) + 1 / (1 - x)

/-- The quantity whose maximum we study. -/
def matF {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  (∏ i, Real.sqrt (lam i)) / (∏ i, (1 - lam i))

/-- The claimed sharp constant. -/
def matC (n : ℕ) : ℝ := (Real.sqrt n / ((n : ℝ) - 1)) ^ n

/-- The box cut out of the simplex by the lower bound `δ` on every coordinate. -/
def Kset (n : ℕ) (δ : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, δ ≤ x i) ∧ ∑ i, x i = 1}

end

end Work.Mostow
