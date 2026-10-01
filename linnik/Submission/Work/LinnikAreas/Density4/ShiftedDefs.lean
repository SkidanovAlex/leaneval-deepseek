/-
# Shared definitions for the estimate `shiftedDivisorSum_le`.

`σ_{-1/2}(n) = Σ_{d ∣ n} d^{-1/2}`, the local Euler factors `f(p) = p^{-1} + g(p)`,
`g(p) = (1+p^{-1/2})^{-1}`, the products `Φ(s) = ∏_{p∈s} f(p)`, `Ψ(s) = ∏_{p∈s} g(p)`,
and the unrestricted divisor sum `Tall r = Σ_{d ∣ r} 1/(d · σ_{-1/2}(r/d))`.
-/
import Mathlib

namespace Work.LinnikAreas.Density4

noncomputable section

open Finset

/-- `σ_{-1/2}(n) = Σ_{d ∣ n} d^{-1/2} = Σ_{d ∣ n} 1/√d`. -/
def sigR (n : ℕ) : ℝ := ∑ d ∈ n.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)

/-- The local Euler factor `g(p) = (1 + p^{-1/2})^{-1}`.  For `p > 0` this is `√p/(1+√p)`. -/
def gR (p : ℕ) : ℝ := (1 + 1 / Real.sqrt (p : ℝ))⁻¹

/-- The local Euler factor `f(p) = p^{-1} + g(p)`. -/
def fR (p : ℕ) : ℝ := 1 / (p : ℝ) + gR p

/-- `Φ(s) = ∏_{p ∈ s} f(p)`. -/
def PhiSh (s : Finset ℕ) : ℝ := ∏ p ∈ s, fR p

/-- `Ψ(s) = ∏_{p ∈ s} g(p)`. -/
def Psi (s : Finset ℕ) : ℝ := ∏ p ∈ s, gR p

/-- The unrestricted divisor sum `Tall r = Σ_{d ∣ r} 1/(d · σ_{-1/2}(r/d))`. -/
def Tall (r : ℕ) : ℝ := ∑ d ∈ r.divisors, (1 : ℝ) / ((d : ℝ) * sigR (r / d))

end

end Work.LinnikAreas.Density4
