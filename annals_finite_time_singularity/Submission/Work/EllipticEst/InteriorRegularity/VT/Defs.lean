/-
Interior regularity of `bslOp α` (weight `(5+α)/α`): the vocabulary of the *localized* strip problem.

This file collects the definitions used by the local Sobolev-regularity argument
(`Work.EllipticEst.InteriorRegularity.bslOp_interiorSmooth`).

The starting point is the strip model of `Strip.lean`: with `s = (1/α) log z` and `θ`, the
unknown is `V = α z · (Ψ · ω)` where `ω = z^((5+α)/α) cos θ`, and the source is
`G = α z · (F · ω)`.  Here:

* `Ws α Ψ x` is the pull-back `ω · Ψ` at the point `x = coords s θ`, i.e.
  `wt α x * Ψ (e^{α s}) θ` with `wt α x = α (e^{α s})^((5+2α)/α) cos θ`, without the strip
  indicator;
* `Vc α Ψ = stripE.indicator (Ws α Ψ)` is `cplx (Vfun α Ψ)` (`Strip.lean`);
* `Gs α F`, `Gc α F` are the corresponding objects for the source.

We also provide the scaled `C^∞` bump `cfun x₀ ρ hρ : E2 → ℂ` with `rIn = ρ`, `rOut = 2ρ`,
i.e. equal to `1` on `closedBall x₀ ρ` and supported in `ball x₀ (2ρ)`, and bounded by `1`.
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.EllipticEst.InteriorRegularity.Strip
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false

/-- The un-indicated pull-back of the unknown `Ψ · ω` to the strip coordinates:
`Ws α Ψ x = wt α x * Ψ (exp (α x₀)) x₁`. -/
def Ws (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : E2 → ℂ :=
  fun x => ((wt α x * Ψ (Real.exp (α * x 0)) (x 1) : ℝ) : ℂ)

/-- The complex unknown of the strip problem, zero off the strip: `Vc α Ψ`. -/
def Vc (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : E2 → ℂ := stripE.indicator (Ws α Ψ)

/-- The un-indicated pull-back of the source `F · ω` to the strip coordinates. -/
def Gs (α : ℝ) (F : ℝ → ℝ → ℝ) : E2 → ℂ :=
  fun x => ((wt α x * F (Real.exp (α * x 0)) (x 1) : ℝ) : ℂ)

/-- The complex source of the strip problem, zero off the strip: `Gc α F`. -/
def Gc (α : ℝ) (F : ℝ → ℝ → ℝ) : E2 → ℂ := stripE.indicator (Gs α F)

/-- The scaled bump function with `rIn = ρ`, `rOut = 2ρ` centred at `x₀`. -/
def cdb (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) : ContDiffBump x₀ :=
  ⟨ρ, 2 * ρ, hρ, by linarith⟩

/-- The complex-valued version of the scaled bump `cdb x₀ ρ hρ`. -/
def cfun (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) : E2 → ℂ :=
  fun x => (((cdb x₀ ρ hρ) x : ℝ) : ℂ)

end Work.EllipticEst.InteriorRegularity.VT
