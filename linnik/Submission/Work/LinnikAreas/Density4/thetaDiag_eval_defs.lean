/-
# Area 4 / HB §11 — definitions for the diagonal evaluation `theta_diag_eval`

This module collects the vocabulary in which the Lean proofs of the pieces of
`Work.LinnikAreas.Density4.theta_diag_eval` are stated.  It is sorry-free.

Setting: `M := w*L > 0`, `W := exp M`, `A := exp (x*L) ≥ W`, `B₀ := exp (u*L)/L² ≤ A`,
`σ := 2-2β ∈ (0,1]`.

* `tdH σ A n := n^{σ-1} e^{-n/A}` — the majorant;
* `tdG M n := min (log n) M` — the exponent of the Graham envelope;
* `tdF ε C₁ M n := ((1+ε) g(n) + C₁) n / M²` — the envelope envelope (without the additive `1`);
* `tdA W n := (Σ_{d|n} θ_M(W) d)²` — the diagonal coefficients;
* `tdS W N` — their partial sums;
* `tdDg M n := n g(n) - (n-1) g(n-1)` — the telescoping increment;
* `tdQ σ A M := Σ_{2 ≤ n ≤ ⌊e^{M-1}⌋} (M - log n - 1) h_n` — the "saving" sum.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-- The majorant `h n = n^{σ-1} e^{-n/A}` of the diagonal evaluation. -/
def tdH (σ A : ℝ) (n : ℕ) : ℝ := (n:ℝ)^(σ-1) * Real.exp (-(n:ℝ)/A)

/-- `g n = min (log n) M`, the exponent shape of Graham's estimate. -/
def tdG (M : ℝ) (n : ℕ) : ℝ := min (Real.log (n:ℝ)) M

/-- The envelope function `F n = ((1+ε) g(n) + C₁) n / M²`. -/
def tdF (ε C₁ M : ℝ) (n : ℕ) : ℝ := ((1+ε)*tdG M n + C₁)*(n:ℝ)/M^2

/-- The diagonal coefficients `a n = (Σ_{d | n} θ_M(W) d)²`. -/
def tdA (W : ℝ) (n : ℕ) : ℝ := (∑ d ∈ n.divisors, thetaM W d)^2

/-- Partial sums of the diagonal coefficients. -/
def tdS (W : ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, tdA W n

/-- The telescoping increment `n g(n) - (n-1) g(n-1)`. -/
def tdDg (M : ℝ) (n : ℕ) : ℝ := (n:ℝ)*tdG M n - ((n:ℝ)-1)*tdG M (n-1)

/-- The "saving" sum `Σ_{2 ≤ n ≤ ⌊e^{M-1}⌋} (M - log n - 1) · n^{σ-1} e^{-n/A}`. -/
def tdQ (σ A M : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (M-1)⌋₊, (M - Real.log (n:ℝ) - 1)*tdH σ A n

end Work.LinnikAreas.Density4
