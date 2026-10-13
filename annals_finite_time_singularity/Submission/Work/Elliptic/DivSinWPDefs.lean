/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted integration-by-parts identity `DivSinIBPWeight`

The lemma `Work.Elliptic.DivSinIBPWeight` relates three weighted integrals of the angular
quotient `u = SinQ h = h / sin(2θ)`:

  `(3 - γ) ∫ cos²(2θ) sin(2θ)^{2-γ} (u')²
      = ∫ sin(2θ)^{4-γ} (u')² - ∫ sin(2θ)^{3-γ} cos(2θ) u' u''`.

Both sides are rewritten via the single integration by parts

  `∫ sin(2θ)^{3-γ} cos(2θ) u' u'' = ∫ s^{4-γ} (u')² - (3-γ) ∫ c² s^{2-γ} (u')²`,

which is the statement `∫ P' = 0` for the primitive

  `P(θ) = -(1/2) sin(2θ)^{3-γ} cos(2θ) (u'(θ))²`,

whose derivative is exactly the difference of the three integrands.  This file fixes the
primitive `DivSinWP`, the three integrands `W1`, `W2`, `W3`, and their difference `WDfun`, so
that the pointwise derivative, the endpoint limits and the integrability can be stated and
proved separately from the final assembly.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- The first integrand `cos(2θ)² sin(2θ)^{2-γ} (u')²` of `DivSinIBPWeight`, where
`u = SinQ h`. -/
def W1 (γ : ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) * (deriv (SinQ h) θ) ^ 2

/-- The second integrand `sin(2θ)^{4-γ} (u')²` of `DivSinIBPWeight`, where `u = SinQ h`. -/
def W2 (γ : ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (Real.sin (2 * θ)) ^ (4 - γ) * (deriv (SinQ h) θ) ^ 2

/-- The third integrand `sin(2θ)^{3-γ} cos(2θ) u' u''` of `DivSinIBPWeight`, where
`u = SinQ h`. -/
def W3 (γ : ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (Real.sin (2 * θ)) ^ (3 - γ) * Real.cos (2 * θ) * deriv (SinQ h) θ
    * deriv (deriv (SinQ h)) θ

/-- The difference of the three integrands of `DivSinIBPWeight`,
`W2 - (3 - γ) W1 - W3`; its integral over `Iθ` vanishes. -/
def WDfun (γ : ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  W2 γ h θ - (3 - γ) * W1 γ h θ - W3 γ h θ

/-- The primitive `P(θ) = -(1/2) sin(2θ)^{3-γ} cos(2θ) (u'(θ))²`, where `u = SinQ h`; its
derivative on `(0, π/2)` is `WDfun`, and it tends to `0` at both endpoints of `Iθ`. -/
def DivSinWP (γ : ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  -(1/2) * (Real.sin (2 * θ)) ^ (3 - γ) * Real.cos (2 * θ) * (deriv (SinQ h) θ) ^ 2

end Work.Elliptic
