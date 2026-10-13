import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.RPFresh.Defs
import Submission.Work.RPFresh.integral_sin_two_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set intervalIntegral

namespace Work.RPFresh

/-- The right-endpoint companion of `integral_sin_two_rpow_le`: for `θ ∈ (0, π/2)`,
`∫_θ^{π/2} sin(2t)^η dt ≤ 2^η (π/2 - θ)^{1+η}/(1+η)`.  Substituting `t = π/2 - u` maps the
integral to the left-endpoint one on `[0, π/2 - θ]` via `sin(π - 2u) = sin(2u)`, and
`sin(2u) ≤ 2u` then gives the bound. -/
theorem integral_sin_two_rpow_le_right {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    (∫ t in θ..(Real.pi/2), (Real.sin (2*t))^(Work.Spaces.eta))
      ≤ 2^(Work.Spaces.eta) * (Real.pi/2 - θ)^(1 + Work.Spaces.eta) / (1 + Work.Spaces.eta) := by
  -- Rewrite `sin (2t) = sin (2 * (π/2 - t))` and reflect the interval.
  have h1 : (∫ t in θ..(Real.pi/2), (Real.sin (2*t))^(Work.Spaces.eta))
      = ∫ t in θ..(Real.pi/2), (Real.sin (2*(Real.pi/2 - t)))^(Work.Spaces.eta) := by
    apply intervalIntegral.integral_congr
    intro t _
    show (Real.sin (2*t))^(Work.Spaces.eta) = (Real.sin (2*(Real.pi/2 - t)))^(Work.Spaces.eta)
    have harg : 2*(Real.pi/2 - t) = Real.pi - 2*t := by ring
    rw [harg, Real.sin_pi_sub]
  have h2 : (∫ t in θ..(Real.pi/2), (Real.sin (2*(Real.pi/2 - t)))^(Work.Spaces.eta))
      = ∫ u in (0:ℝ)..(Real.pi/2 - θ), (Real.sin (2*u))^(Work.Spaces.eta) := by
    have h := intervalIntegral.integral_comp_sub_left (a := θ) (b := Real.pi/2)
      (fun u : ℝ => (Real.sin (2*u))^(Work.Spaces.eta)) (Real.pi/2)
    simpa using h
  -- The reflected interval lies in `(0, π/2)`.
  have hθ' : (Real.pi/2 - θ) ∈ Set.Ioo (0:ℝ) (Real.pi/2) :=
    ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hmain := integral_sin_two_rpow_le (θ := Real.pi/2 - θ) hθ'
  rw [h1, h2]
  exact hmain

end Work.RPFresh
