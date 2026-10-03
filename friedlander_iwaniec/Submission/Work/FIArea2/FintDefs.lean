/-
# The Fourier integral `F(u₁,u₂)` of *FI* §7

*FI* (7.1) is `F(u₁,u₂) = ∫∫ f(g(t₁,t₂)) e(u₁t₁+u₂t₂) dt₁dt₂` with
`g(t₁,t₂) = t₁⁴ − 2γt₁²t₂² + t₂⁴` and `e(x) = exp(2πix)`.  This module fixes that object (and its
`γ = 0` specialisation), so that the bounds of Lemma 7.1 can be stated as self-contained lemmas
about `Fint`.
-/
import Mathlib

set_option autoImplicit false

namespace Work.FIArea2

noncomputable section

open scoped BigOperators

/-- **The Fourier integral (7.1)** of *FI* §7:
`F(u₁,u₂) = ∫_{ℝ²} f(t₁⁴ − 2γt₁²t₂² + t₂⁴)·e(u₁t₁ + u₂t₂) dt₁dt₂`, `e(x) = exp(2πix)`. -/
def Fint (f : ℝ → ℝ) (γ u₁ u₂ : ℝ) : ℂ :=
  ∫ t : ℝ × ℝ, ((f (t.1 ^ 4 - 2 * γ * t.1 ^ 2 * t.2 ^ 2 + t.2 ^ 4) : ℝ) : ℂ)
    * Complex.exp (2 * Real.pi * Complex.I * (u₁ * t.1 + u₂ * t.2))

/-- The `h = (h₁,h₂)` frequency of (6.9): `u₁ = h₁|Δz₂|^{-1/2}`, `u₂ = h₂|Δz₁|^{-1/2}` — recorded
here only through the *scale* `H = M^{-1/4}N^{3/4}` of Lemma 7.1: `u_j²δ√M = h_j²/H²`. -/
def Hscale (M N : ℝ) : ℝ := M ^ (-(1 : ℝ) / 4) * N ^ ((3 : ℝ) / 4)

end

end Work.FIArea2
