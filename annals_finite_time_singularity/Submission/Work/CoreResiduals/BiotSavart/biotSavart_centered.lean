import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Work.CoreResiduals.Defs
import Submission.Work.StabilityFar.Decay.biotSavart_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

/-- **The centred form of the Biot–Savart integral.**  The kernel `bsK ω x a = ‖x-a‖⁻³ • (ω a ⨯ (x-a))` is supported in `closedBall x ρ` as soon as `ω` is supported in `closedBall 0 R` and `R + ‖x‖ ≤ ρ`; hence the full Bochner integral equals its restriction to `Metric.ball x ρ`.  This is the prerequisite of the Calderón–Zygmund regularisation of the `x`-derivative of `biotSavart`. -/
theorem biotSavart_centered {ω : Work.LWP.R3 → Work.LWP.R3} {R M ρ : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) {x : Work.LWP.R3}
    (hρ : R + ‖x‖ ≤ ρ) :
    Work.LWP.biotSavart ω x
      = (4 * Real.pi)⁻¹ • ∫ a in Metric.ball x ρ, Work.LWP.BiotSavart.bsK ω x a := by
  -- `hM`, `hbdd` and `hm` (together with `hs`) only serve to make `bsK ω x` a Bochner
  -- integrable function: the *singular* kernel sits at the centre `x` of the ball
  -- `B(0,R) ⊆ B(x, ‖x‖ + R)`, where `‖x - ·‖⁻²` is an integrable majorant
  -- (`Work.StabilityFar.Decay.integrable_bsK_supported`).
  have _hi : MeasureTheory.Integrable (Work.LWP.BiotSavart.bsK ω x) MeasureTheory.volume :=
    Work.StabilityFar.Decay.integrable_bsK_supported hM hbdd hs hm x
  -- The only *set* of points of the support of the integrand that lies outside `ball x ρ` is
  -- contained in the sphere `sphere x ρ`, which has measure zero.
  have hsphere : MeasureTheory.volume (Metric.sphere x ρ) = 0 :=
    MeasureTheory.Measure.addHaar_sphere MeasureTheory.volume x ρ
  have hkey : ∫ y, Work.LWP.BiotSavart.bsK ω x y
      = ∫ y in Metric.ball x ρ, Work.LWP.BiotSavart.bsK ω x y := by
    -- rewrite the restricted integral as the integral of the corresponding indicator
    rw [← MeasureTheory.integral_indicator (μ := MeasureTheory.volume)
      (f := Work.LWP.BiotSavart.bsK ω x) measurableSet_ball]
    refine MeasureTheory.integral_congr_ae ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    -- it is enough that the integrand and its indicator agree off the null sphere
    refine MeasureTheory.measure_mono_null ?_ hsphere
    intro a ha
    rw [Set.mem_ofPred_eq] at ha
    by_cases hmem : a ∈ Metric.ball x ρ
    · -- inside the ball the indicator is the integrand itself
      rw [Set.indicator_of_mem hmem] at ha
      exact absurd rfl ha
    · -- outside the ball the indicator vanishes, so `bsK ω x a ≠ 0`: the support hypothesis
      -- gives `‖a‖ ≤ R`, whence `‖x - a‖ ≤ R + ‖x‖ ≤ ρ`, while `a ∉ ball x ρ` gives `ρ ≤ ‖x - a‖`
      have hzero : (Metric.ball x ρ).indicator (Work.LWP.BiotSavart.bsK ω x) a = 0 :=
        Set.indicator_of_notMem hmem _
      have hb : Work.LWP.BiotSavart.bsK ω x a ≠ 0 := fun h0 => ha (by rw [hzero, h0])
      have hωa : ω a ≠ 0 := fun h0 => hb (Work.LWP.BiotSavart.bsK_eq_zero h0)
      have haR : a ∈ Metric.closedBall (0 : Work.LWP.R3) R := hs a hωa
      have h1 : dist a x ≤ ρ := by
        have h2 : dist a 0 ≤ R := Metric.mem_closedBall.mp haR
        have h3 : dist a x ≤ dist a 0 + dist 0 x := dist_triangle a 0 x
        have h4 : dist (0 : Work.LWP.R3) x = ‖x‖ := dist_zero_left x
        linarith
      have h5 : ρ ≤ dist a x := not_lt.mp hmem
      exact Metric.mem_sphere.mpr (le_antisymm h1 h5)
  rw [Work.LWP.BiotSavart.biotSavart_apply, hkey]

end Work.CoreResiduals.BiotSavart
