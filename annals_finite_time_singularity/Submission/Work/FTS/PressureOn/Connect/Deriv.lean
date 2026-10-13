/-
# `Work.FTS.PressureOn.Connect.Deriv` — the time derivative of the potential `q`

`potTDeriv ω x t` is the value of `∂_t q(x,t)` for the reconstructed potential
`q = potOn ω = pressurePotential (lamb (physVel ω) ω · t)`:
`∂_t q(x,t) = -∫ ⟪∇N(x-y), ∂_t (u×ω)(y,t)⟫ dy` (`hasDerivAt_pressurePotential_time_of_continuous`).
It is the `t`-component of the derivative of `q.uncurry`, and it is used both for the joint `C¹` of
the pressure and for the one-sided `C¹` at the boundary time `t = 0`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.EulerAssembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory
open Work.FTS.Physical (physVel)
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

noncomputable section

/-- **The time derivative of the reconstructed potential**:
`potTDeriv ω x t = -∫ y, ⟪∇Nfund (x - y), ∂_t(u × ω)(y,t)⟫`. -/
noncomputable def potTDeriv (ω : R3 → ℝ → R3) (x : R3) (t : ℝ) : ℝ :=
  -∫ y, inner ℝ (nablaNfund (x - y))
    (FiniteTimeSingularity.timeDeriv (lamb (physVel ω) ω) y t)

theorem potTDeriv_apply (ω : R3 → ℝ → R3) (x : R3) (t : ℝ) :
    potTDeriv ω x t = -∫ y, inner ℝ (nablaNfund (x - y))
      (FiniteTimeSingularity.timeDeriv (lamb (physVel ω) ω) y t) := rfl

/-- The `x`-component of the derivative of `q.uncurry`: `innerSL Φ` with
`Φ = ∂_t u - u×ω`. -/
noncomputable def potGradCLM (ω : R3 → ℝ → R3) (x : R3) (t : ℝ) : R3 →L[ℝ] ℝ :=
  innerSL ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) x t
    - crossVec (physVel ω x t) (ω x t))

/-- The full derivative of `q.uncurry` at `(x,t)`, as a continuous linear map on `R3 × ℝ`. -/
noncomputable def potFDeriv (ω : R3 → ℝ → R3) (x : R3) (t : ℝ) : R3 × ℝ →L[ℝ] ℝ :=
  (potGradCLM ω x t).comp (ContinuousLinearMap.fst ℝ R3 ℝ)
    + ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ R3 ℝ) (potTDeriv ω x t)

end

end Work.FTS.PressureOn.Connect
