/-
# `Work.FIArea7.AngFourier` — the Fourier coefficients of the angular mollifier, *FI* (16.26)

The angular mollifier of *FI* (5.12) is a `C²` function `q` of the angle, of width `≍ θ`, with the
§7 derivative bounds `|q^{(j)}| ≤ c_j θ^{-j}` (`j ≤ 2`) — this is exactly the `q` of
`Work.FITop4.IsBetaCoeff6`.  *FI* uses its truncated Fourier series twice:

* (16.26)–(16.27) in §16/§17, `q(α) = Σ_{|ℓ|≤L} q̂(ℓ)e^{iℓα} + O(θ^{-1}L^{-1})`, with the
  coefficient bound (16.26) `q̂(ℓ) ≪ θ(1 + θ²ℓ²)^{-1}`;
* (20.17)–(20.19) for the square wave `t(α) = sign(cos α)` in §20–§23.

This file defines the Fourier coefficient (as the integral over one period) and fixes the statement
of (16.26) as the lemma `angFourierCoeff_le` (delegated); the expansion/truncation lemma (16.27)
and the step-function analogue used by the reflection sign of `reflSymbol_separable` are separate
items.
-/
import Mathlib

set_option autoImplicit false

namespace Work.FIArea7

open MeasureTheory intervalIntegral
open scoped BigOperators

noncomputable section

/-- **The Fourier coefficient** `ŵ(ℓ) = (1/2π)∫₀^{2π} w(α)e^{-iℓα}dα` of a function of the angle.

`w` is not assumed periodic: it is used below only for functions supported in `(0, 2π)`, for which
the integral over one period is the full integral. -/
def angFourierCoeff (w : ℝ → ℂ) (ℓ : ℤ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ α in (0 : ℝ)..(2 * Real.pi), w α * Complex.exp (-(Complex.I * (ℓ : ℂ) * (α : ℂ)))

end

end Work.FIArea7
