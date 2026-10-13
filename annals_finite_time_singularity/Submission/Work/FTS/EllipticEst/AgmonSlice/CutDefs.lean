/-
Copyright: work module for the Elgindi finite-time singularity project.

# Cut-off bookkeeping for the finiteness of `∫ ρ (z h')²`

This module fixes the notation shared by the proof of

  `Work.FTS.EllipticEst.AgmonSlice.rDz_lintegral_ne_top`:

with the radial weight `w z = (1+z)²/z²` (`Work.Spaces.w`) and `ρ = w² = cutRho`, and a
cut-off `ψ` (in the application `ψ = psiFun φ k`, `φ` a smooth bump),

* `cutU h ψ = ρ z ψ² (z h')` is the function `u` of the integration by parts;
* `cutF h ψ = ρ ψ² (z h')² = u · h'` is the integrand whose finiteness is the target;
* `cutHs h ψ = ρ ψ² h²`, `cutH h = ρ h²`, `cutQs h ψ = ρ ψ² (z² h'')²` are the three squares
  against which `cutF` is estimated (the cut-off square, the plain square, and the second
  derivative square of the Agmon inequality).

The Agmon estimate at cut-off level `χ` is obtained from the identity

  `cutF h ψ = (cutU h ψ · h)' - (cutU h ψ)' · h`

by integrating (the boundary term vanishes because `supp ψ` is compact in `(0,∞)`) and using
`|(ρ z)'| ≤ 3ρ`, `|2 ρ z ψ ψ'| ≤ 2 K ρ` and `ρ z ψ² (z h')' = ρ ψ² (z² h'' + z h')`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AgmonSlice

set_option autoImplicit false

/-- `ρ = w²`, the square of the radial weight `w z = (1+z)²/z²`. -/
def cutRho (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

/-- The function `u = ρ z χ² (z h')` of the integration by parts. -/
def cutU (h ψ : ℝ → ℝ) (y : ℝ) : ℝ := cutRho y * y * ψ y ^ 2 * (y * deriv h y)

/-- The integrand `ρ χ² (z h')² = u · h'` of the Agmon estimate. -/
def cutF (h ψ : ℝ → ℝ) (z : ℝ) : ℝ := cutRho z * ψ z ^ 2 * (z * deriv h z) ^ 2

/-- `ρ χ² h²`. -/
def cutHs (h ψ : ℝ → ℝ) (z : ℝ) : ℝ := cutRho z * ψ z ^ 2 * (h z) ^ 2

/-- `ρ h²`. -/
def cutH (h : ℝ → ℝ) (z : ℝ) : ℝ := cutRho z * (h z) ^ 2

/-- `ρ χ² (z² h'')²`. -/
def cutQs (h ψ : ℝ → ℝ) (z : ℝ) : ℝ :=
  cutRho z * ψ z ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2

@[simp] theorem cutRho_nonneg (z : ℝ) : 0 ≤ cutRho z := by
  rw [cutRho]; positivity

theorem cutU_apply (h ψ : ℝ → ℝ) (y : ℝ) :
    cutU h ψ y = cutRho y * y * ψ y ^ 2 * (y * deriv h y) := rfl

/-- `cutU h ψ · h' = cutF h ψ`, the pointwise identity behind the integration by parts. -/
theorem cutU_mul_deriv (h ψ : ℝ → ℝ) (z : ℝ) :
    cutU h ψ z * deriv h z = cutF h ψ z := by
  simp only [cutU, cutF]
  ring

end Work.FTS.EllipticEst.AgmonSlice
