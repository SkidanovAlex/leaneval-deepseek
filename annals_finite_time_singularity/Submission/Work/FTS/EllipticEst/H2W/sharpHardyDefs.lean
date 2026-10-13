/-
Copyright: work module for the Elgindi finite-time singularity project.

# Definitions behind the sharp slice Hardy inequality `sharpHardy_slice`

The target inequality

  `∫_{Iθ} v² cos²(2θ) sin(2θ)^{-2-η} ≤ 1/(1+η)² ∫_{Iθ} (v')² sin(2θ)^{-η} + 100 (∫ v² + ∫ (v')²)`

is proved by the *completion of squares*

  `0 ≤ ∫ (v' sin(2θ)^{-η/2} - (1+η) v cos(2θ) sin(2θ)^{-1-η/2})²`,

whose integrand is the derivative of the boundary quantity

  `gFn η v θ = v θ ² · cos (2θ) · sin (2θ)^{-(1+η)}`

(which vanishes at both endpoints `0, π/2` when `v 0 = v (π/2) = 0`, because the `C¹`-bound
`v θ = O(min (θ, π/2 - θ))` beats the singular weight `sin(2θ)^{-(1+η)}` as `η < 1`).

This file only records the two objects that the main proof and the auxiliary lemmas share:

* `gFn η v`   — the boundary quantity above,
* `gDeriv η v` — its derivative on the open interval `(0, π/2)`.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

/-- The boundary quantity of the sharp angular Hardy inequality:
`gFn η v θ = v θ ² * cos (2θ) * sin (2θ) ^ (-(1+η))`. -/
def gFn (η : ℝ) (v : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (v θ) ^ 2 * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η))

/-- The derivative of `gFn η v` on `(0, π/2)`:

`gDeriv η v θ = 2 v v' cos(2θ) sin(2θ)^{-(1+η)} - 2 v² sin(2θ)^{-η}
                  - 2 (1+η) v² cos²(2θ) sin(2θ)^{-(2+η)}`. -/
def gDeriv (η : ℝ) (v : ℝ → ℝ) (θ : ℝ) : ℝ :=
  2 * ((v θ) * deriv v θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + η)))
    - 2 * ((v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
    - 2 * (1 + η) * ((v θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η))

end Work.FTS.EllipticEst.H2W
