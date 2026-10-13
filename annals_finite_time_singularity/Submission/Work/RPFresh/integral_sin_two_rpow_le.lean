import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set intervalIntegral

namespace Work.RPFresh

/-- For `θ ∈ (0, π/2)`, the `η`-power of `sin(2t)` is integrable on `[0,θ]` against the
majorant `(2t)^η`, and the resulting integral is bounded by `2^η θ^{1+η}/(1+η)`.  This is
the elementary estimate used to control the `sin(2θ)^η` weight near the endpoints
`θ = 0, π/2`; note it only needs `sin x ≤ x` and the monotonicity of `x ↦ x^η` for `η > 0`. -/
theorem integral_sin_two_rpow_le {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    (∫ t in (0:ℝ)..θ, (Real.sin (2*t))^(Work.Spaces.eta))
      ≤ 2^(Work.Spaces.eta) * θ^(1 + Work.Spaces.eta) / (1 + Work.Spaces.eta) := by
  have hη : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  have h0θ : (0:ℝ) ≤ θ := le_of_lt hθ.1
  -- Pointwise domination `sin(2t)^η ≤ (2t)^η` on `[0,θ]`, hence integral domination.
  have hcont1 : Continuous fun t : ℝ => (Real.sin (2*t))^(Work.Spaces.eta) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
      (fun x => Or.inr hη.le)
  have hcont2 : Continuous fun t : ℝ => (2*t)^(Work.Spaces.eta) :=
    (continuous_const.mul continuous_id).rpow_const (fun x => Or.inr hη.le)
  have hmono : (∫ t in (0:ℝ)..θ, (Real.sin (2*t))^(Work.Spaces.eta))
      ≤ ∫ t in (0:ℝ)..θ, (2*t)^(Work.Spaces.eta) := by
    apply intervalIntegral.integral_mono_on h0θ (hcont1.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _)
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hs : Real.sin (2*x) ≤ 2*x := Real.sin_le (by linarith)
    have hsnn : 0 ≤ Real.sin (2*x) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
        linarith [hθ.2, Real.pi_pos, hx0, hx.2]
    exact Real.rpow_le_rpow hsnn hs hη.le
  -- Evaluate the majorant integral.
  have hstep : (∫ t in (0:ℝ)..θ, (2*t)^(Work.Spaces.eta))
      = 2^(Work.Spaces.eta) * ∫ t in (0:ℝ)..θ, t^(Work.Spaces.eta) := by
    rw [← intervalIntegral.integral_const_mul (2^(Work.Spaces.eta))
      (fun t => t^(Work.Spaces.eta))]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := by
      have h := ht.1
      rw [min_eq_left h0θ] at h
      exact h
    exact Real.mul_rpow (by norm_num) ht0
  have hrpow : (∫ t in (0:ℝ)..θ, t^(Work.Spaces.eta))
      = θ^(Work.Spaces.eta + 1)/(Work.Spaces.eta + 1) := by
    rw [integral_rpow]
    · rw [Real.zero_rpow (by linarith)]
      ring
    · exact Or.inl (by linarith)
  calc (∫ t in (0:ℝ)..θ, (Real.sin (2*t))^(Work.Spaces.eta))
      ≤ ∫ t in (0:ℝ)..θ, (2*t)^(Work.Spaces.eta) := hmono
    _ = 2^(Work.Spaces.eta) * ∫ t in (0:ℝ)..θ, t^(Work.Spaces.eta) := hstep
    _ = 2^(Work.Spaces.eta) * (θ^(Work.Spaces.eta + 1)/(Work.Spaces.eta + 1)) := by
          rw [hrpow]
    _ = 2^(Work.Spaces.eta) * θ^(1 + Work.Spaces.eta) / (1 + Work.Spaces.eta) := by
          have h1 : (1:ℝ) + Work.Spaces.eta = Work.Spaces.eta + 1 := by ring
          rw [h1]; ring

end Work.RPFresh
