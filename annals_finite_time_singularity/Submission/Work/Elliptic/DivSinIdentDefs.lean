/-
Copyright: work module for the Elgindi finite-time singularity project.

# The antiderivative behind the second-order identity `DivSinIdentityB`

`DivSinIdentityB` is the *second-order* weighted integration-by-parts identity for the
angular quotient `u = SinQ h = h / sin(2θ)`, companion to the first-order identity
`DivSinIdentityA`.  Writing `s = sin(2θ)`, `c = cos(2θ)`, both sides of the identity
differ by a total derivative, namely the derivative of

  `DivSinB γ h θ = sin(2θ)^{3-γ} · F₁(θ)`,

with `F₁ = 4c (u')² - 8 s u' u + 8(2-γ) c u²`.  This file fixes that antiderivative (and the
integrator `F₁`), together with the difference `Dfun` of the two integrands, so that the
pointwise computation and the final Fundamental Theorem of Calculus step can be stated
separately.

All exponents are real powers (`Real.rpow`); the relevant interval is `Iθ = [0, π/2]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.DivSinBddDefs
import Submission.Work.Elliptic.DivSinDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- The bracket `F₁(θ) = 4 cos(2θ)·(u'(θ))² - 8 sin(2θ)·u'(θ)·u(θ) + 8(2-γ) cos(2θ)·(u(θ))²`
(where `u = SinQ h`) appearing in the antiderivative `DivSinB`. -/
def DivSinF1 (γ : ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (4 * Real.cos (2 * θ)) * (deriv (SinQ h) θ) ^ 2
    - (8 * Real.sin (2 * θ)) * (deriv (SinQ h) θ * SinQ h θ)
    + (8 * (2 - γ) * Real.cos (2 * θ)) * (SinQ h θ) ^ 2

/-- The antiderivative `B(θ) = sin(2θ)^{3-γ} · F₁(θ)`: its derivative is the difference
between the two integrands of `DivSinIdentityB`.  It tends to `0` at both endpoints, which is
what makes the boundary terms of the integration by parts vanish. -/
def DivSinB (γ : ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (Real.sin (2 * θ)) ^ (3 - γ) * DivSinF1 γ h θ

/-- The difference of the two integrands of `DivSinIdentityB`: the left hand side integrand
`(h'')² sin(2θ)^{2-γ}` minus the right hand side integrand. -/
def Dfun (γ : ℝ) (h : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  (deriv (deriv h) θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
    - ((Real.sin (2 * θ)) ^ (4 - γ) * (deriv (deriv (SinQ h)) θ) ^ 2
      + 8 * (γ - 1) * ((Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
          * (deriv (SinQ h) θ) ^ 2)
      + 16 * ((Real.sin (2 * θ)) ^ (4 - γ) * (deriv (SinQ h) θ) ^ 2)
      + 16 * (3 - γ) * ((Real.sin (2 * θ)) ^ (4 - γ) * (SinQ h θ) ^ 2)
      - 16 * (2 - γ) * (3 - γ) * ((Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)
          * (SinQ h θ) ^ 2))

/-! ## Derivatives of the elementary angular functions -/

/-- `HasDerivAt` form of `deriv (sin (2θ)) = 2 cos (2θ)`. -/
lemma hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  convert h2 using 1; ring

/-- `HasDerivAt` form of `deriv (cos (2θ)) = -2 sin (2θ)`. -/
lemma hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-2 * Real.sin (2 * θ)) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-Real.sin (2 * θ) * 2) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ h1
  convert h2 using 1; ring

/-- `sin (2θ) > 0` on the open interval `(0, π/2)`. -/
lemma sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

end Work.Elliptic
