/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary definitions for the `I₄` lower bound

This module owns the two objects of the paper's `I₄` computation
(T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021, Step 2 of the
proof of Proposition `prop:H2`, tex 895–915):

* the coefficient `A(θ) = ((1-η)/2)·cos 2θ + 2 sin²θ` of the identity, which is
  nonnegative (and bounded above by `2`), and
* the primitive `Gprim u` and its derivative `Hintegrand u` of the slice identity:
  writing `Ψ̄ = u / cos θ`, one has
  `Gprim u = (1/2)·(sin θ cos θ·σ(θ))·((Ψ̄)'(θ)² - Ψ̄(θ)²)` and
  `Hintegrand u = A(θ)(Ψ̄)'(θ)²σ(θ) + sin θ·(Ψ̄)'(θ)·u''(θ)·σ(θ)
                    - ((1-η)/2)cos 2θ·Ψ̄(θ)²σ(θ)`,
  where `σ(θ) = sin(2θ)^{-η}` is `sig` of `Submission.Work.FTS.EllipticEst.AngSecond.Defs`.

The point of the two definitions is the identity `∫ Hintegrand u = 0` (proved from the
fundamental theorem of calculus once one knows `HasDerivAt (Gprim u) (Hintegrand u θ) θ`
on the open interval and that `Gprim u` tends to `0` at both endpoints) which rearranges,
after multiplying by `w z²` and integrating in `z`, to the `I₄` lower bound.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The coefficient `A(θ) = ((1-η)/2)·cos 2θ + 2 sin²θ` of the `I₄`-identity. -/
def acoef (θ : ℝ) : ℝ := ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ) + 2 * (Real.sin θ) ^ 2

/-- The primitive `G(θ) = (1/2)·sin θ cos θ·σ(θ)·((u/cos)'(θ)² - (u/cos)(θ)²)` of the
`I₄`-identity, where `σ = sig`. -/
def Gprim (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (1 / 2) * (Real.sin θ * Real.cos θ * sig θ)
    * ((deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 - (u θ / Real.cos θ) ^ 2)

/-- The derivative of `Gprim u` on `(0, π/2)`: the integrand of the `I₄`-identity. -/
def Hintegrand (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  acoef θ * (deriv (fun θ' => u θ' / Real.cos θ') θ) ^ 2 * sig θ
    + Real.sin θ * deriv (fun θ' => u θ' / Real.cos θ') θ * deriv (deriv u) θ * sig θ
    - ((1 - Work.Spaces.eta) / 2) * Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2 * sig θ

/-- `1 - η > 0`, where `η = 99/100`. -/
theorem one_sub_eta_pos : 0 < 1 - Work.Spaces.eta := by
  rw [Work.Spaces.eta]; norm_num

/-- `A(θ) = (1-η)/2 + (1+η)·sin²θ`, the form in which nonnegativity is visible. -/
theorem acoef_eq (θ : ℝ) :
    acoef θ = (1 - Work.Spaces.eta) / 2 + (1 + Work.Spaces.eta) * (Real.sin θ) ^ 2 := by
  have hc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    linarith [Real.cos_sq_add_sin_sq θ]
  rw [acoef, Real.cos_two_mul, hc]; ring

theorem acoef_nonneg (θ : ℝ) : 0 ≤ acoef θ := by
  rw [acoef_eq]
  have h2 : (0:ℝ) ≤ (Real.sin θ) ^ 2 := sq_nonneg _
  have h4 : (0:ℝ) ≤ 1 + Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have h3 : (0:ℝ) < 1 - Work.Spaces.eta := one_sub_eta_pos
  nlinarith

theorem acoef_le_two (θ : ℝ) : acoef θ ≤ 2 := by
  have hsin : (Real.sin θ) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_le_one θ]
  rw [acoef_eq]
  have h1 : Work.Spaces.eta = 99 / 100 := rfl
  nlinarith [hsin, h1]

theorem abs_acoef_le_two (θ : ℝ) : |acoef θ| ≤ 2 :=
  abs_le.mpr ⟨by linarith [acoef_nonneg θ], acoef_le_two θ⟩

end Work.FTS.EllipticEst.AngSecond
