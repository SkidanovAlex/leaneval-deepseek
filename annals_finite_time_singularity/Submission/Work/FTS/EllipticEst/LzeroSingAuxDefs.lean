/-
Work module for the Elgindi finite-time singularity project.

# Helper definitions for the ODE of the singular solution `LzeroSing`

`LzeroSing θ = sin(2θ) · ∫_{π/4}^{π/2-θ} ds/(sin s · sin(2s)²)` (see `LzeroSingDefs`).
This module names the three natural pieces of the computation that `LzeroSing` solves
`LzeroSing'' = (tan · LzeroSing)' - 6 LzeroSing` (i.e. `-y'' + (tan y)' - 6y = 0`) on
`(0, π/2)`:

* `SingInt θ` — the reduction-of-order integral;
* `SingY1 θ` — the value of `deriv LzeroSing θ` (computed by the product rule and the
  fundamental theorem of calculus: `2 cos(2θ)·I(θ) - 1/(cos θ · sin 2θ)`);
* `SingY2 θ` — the value of `deriv (deriv LzeroSing) θ`
  (`-4 sin(2θ)·I(θ) - sin θ/(cos²θ · sin 2θ)`).

The companion module `Submission/Work/FTS/EllipticEst/LzeroSingODE.lean` proves
`HasDerivAt SingInt`, `HasDerivAt LzeroSing` with value `SingY1`, `HasDerivAt SingY1` with value
`SingY2`, and the final algebraic identity.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.LzeroSingDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

/-- The reduction-of-order integral `∫_{π/4}^{π/2-θ} ds/(sin s · sin(2s)²)`, so that
`LzeroSing θ = sin(2θ) · SingInt θ`. -/
def SingInt (θ : ℝ) : ℝ :=
  ∫ s in (Real.pi / 4)..(Real.pi / 2 - θ), LzeroSingIntegrand s

/-- The derivative of `LzeroSing`: `2 cos(2θ)·I(θ) - 1/(cos θ · sin 2θ)`. -/
def SingY1 (θ : ℝ) : ℝ :=
  2 * Real.cos (2 * θ) * SingInt θ - 1 / (Real.cos θ * Real.sin (2 * θ))

/-- The second derivative of `LzeroSing`: `-4 sin(2θ)·I(θ) - sin θ/(cos²θ · sin 2θ)`. -/
def SingY2 (θ : ℝ) : ℝ :=
  -4 * Real.sin (2 * θ) * SingInt θ - Real.sin θ / (Real.cos θ ^ 2 * Real.sin (2 * θ))

theorem LzeroSing_eq_sin_mul_SingInt (θ : ℝ) :
    LzeroSing θ = Real.sin (2 * θ) * SingInt θ := rfl

theorem SingY1_apply (θ : ℝ) :
    SingY1 θ = 2 * Real.cos (2 * θ) * SingInt θ - 1 / (Real.cos θ * Real.sin (2 * θ)) := rfl

theorem SingY2_apply (θ : ℝ) :
    SingY2 θ = -4 * Real.sin (2 * θ) * SingInt θ
      - Real.sin θ / (Real.cos θ ^ 2 * Real.sin (2 * θ)) := rfl

end Work.FTS.EllipticEst
