import Mathlib

/-!
# The averaged-interval kernel `trapK`

This file fixes the single object out of which the sharp mean value theorem for
`δ`-separated frequencies (`Work.ZeroDensity.HB7MvtMul`) is built.

For `L, W : ℝ` and a real frequency `ν`, put

  `trapK L W ν = W⁻¹ ∫_{0}^{W} ∫_{s}^{s+L} exp (-(2πi ν t)) dt ds`.

Equivalently, `trapK L W ν` is the Fourier transform, evaluated at `ν`, of the *trapezoid*
weight `Ψ(t) = W⁻¹ ∫_{0}^{W} 1_{[s,s+L]}(t) ds`, which equals `1` on `[W,L]` (when `W ≤ L`),
vanishes outside `[0,L+W]`, and satisfies `∫ Ψ = L`.

The point of the averaging over `s` is the resulting *quadratic* decay
`‖trapK L W ν‖ ≤ 1/(W π² ν²)` away from `ν = 0`: this is what makes the double sum
`∑_{i,j} ζ_i \bar ζ_j trapK L W (γ_i - γ_j)` summable along a `δ`-separated set of
frequencies (whereas the single rectangle `1_{[0,L]}` decays only like `1/|ν|` and is not
summable in that way).  Combined with the covering trick (`[a,b] ⊆ [s,s+L]` for every
`s ∈ [a-W, a]` when `L ≥ b-a+W`) this yields the sharp coefficient `b - a` for the length
of the interval, which the multiplicative statement forces (`m = 1`).
-/

open scoped BigOperators

noncomputable section

namespace Work.ZeroDensity

/-- The averaged-interval kernel, as a double interval integral of the exponential
`exp (-(2πi ν t))`. -/
def trapK (L W ν : ℝ) : ℂ :=
  ((W : ℂ))⁻¹ * ∫ s in (0 : ℝ)..W,
    ∫ t in s..(s + L), Complex.exp (-(2 * Real.pi * Complex.I * (ν : ℂ) * (t : ℂ)))

end Work.ZeroDensity
