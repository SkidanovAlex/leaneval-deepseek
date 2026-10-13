import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Work.CoreResiduals.BiotSavart.DerivDefs
import Submission.Work.CoreResiduals.BiotSavart.biotSavart_centered

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals.BiotSavart

open MeasureTheory Metric
open Work.StabilityFar.Decay (kf crossL)

/-- **The Biot–Savart field as an integral over the fixed ball `B(0,ρ)`.**

The Newtonian-potential Biot–Savart field is the full-space Bochner integral of the kernel
`bsK ω x a = ‖x-a‖⁻³ • (ω a × (x-a))`.  When `ω` is supported in `closedBall 0 R` and
`R + ‖x‖ ≤ ρ`, the support of the integrand misses `B(0,ρ)ᶜ` up to the sphere `sphere 0 ρ`,
which is `volume`-null; hence the full integral coincides with the integral over `B(0,ρ)`.

Since the restricted integrand is `crossL (ω a) (kf (x-a))` (`bsK_eq_crossL`), this identifies
`biotSavart ω x` with `(4π)⁻¹ • bsField ω ρ x` — the un-normalised field on which the
Calderón–Zygmund differentiation of the Biot–Savart operator is carried out. -/
theorem biotSavart_ball_integral {ω : Work.LWP.R3 → Work.LWP.R3} {R M ρ : ℝ} (hM : 0 ≤ M)
    (hbdd : ∀ a, ‖ω a‖ ≤ M) (hs : ∀ a, ω a ≠ 0 → a ∈ Metric.closedBall 0 R)
    (hm : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume) {x : Work.LWP.R3}
    (hρ : R + ‖x‖ ≤ ρ) :
    Work.LWP.biotSavart ω x = (4 * Real.pi)⁻¹ • Work.CoreResiduals.BiotSavart.bsField ω ρ x := by
  -- `R + ‖x‖ ≤ ρ` gives in particular `R ≤ ρ`, so the support of `ω` lies in `closedBall 0 ρ`.
  have hRle : R ≤ ρ := by have := norm_nonneg x; linarith
  -- The kernel scalar `(4π)⁻¹` is common to both sides; the content is the identity of the
  -- underlying Bochner integrals.
  have hkey : ∫ y, Work.LWP.BiotSavart.bsK ω x y
      = ∫ a in Metric.ball (0 : Work.LWP.R3) ρ, crossL (ω a) (kf (x - a)) := by
    -- Replace the integrand by its indicator on `B(0,ρ)` (an a.e. equality) and then unfold the
    -- restricted integral into the integral of that indicator.
    rw [← MeasureTheory.integral_indicator (μ := MeasureTheory.volume)
      (f := fun a => crossL (ω a) (kf (x - a))) measurableSet_ball]
    refine MeasureTheory.integral_congr_ae ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    -- The two integrands can only differ on points of `sphere 0 ρ`, a null set.
    refine MeasureTheory.measure_mono_null ?_
      (MeasureTheory.Measure.addHaar_sphere MeasureTheory.volume (0 : Work.LWP.R3) ρ)
    intro a ha
    rw [Set.mem_ofPred_eq] at ha
    by_cases hmem : a ∈ Metric.ball (0 : Work.LWP.R3) ρ
    · -- Inside the ball the indicator is the integrand itself, so the two sides agree there.
      exact absurd (by rw [Set.indicator_of_mem hmem,
        Work.StabilityFar.Decay.bsK_eq_crossL]) ha
    · -- Outside the ball the indicator vanishes; a non-vanishing kernel forces `ω a ≠ 0`,
      -- hence `‖a‖ ≤ R ≤ ρ`, so `dist a 0 = ρ` and `a` lies on the null sphere.
      have hzero : (Metric.ball (0 : Work.LWP.R3) ρ).indicator
          (fun a => crossL (ω a) (kf (x - a))) a = 0 := Set.indicator_of_notMem hmem _
      have hb : Work.LWP.BiotSavart.bsK ω x a ≠ 0 := fun h0 => ha (by rw [hzero, h0])
      have hωa : ω a ≠ 0 := fun h0 => hb (Work.LWP.BiotSavart.bsK_eq_zero h0)
      have haR : dist a 0 ≤ R := Metric.mem_closedBall.mp (hs a hωa)
      have h5 : ρ ≤ dist a 0 := not_lt.mp hmem
      exact Metric.mem_sphere.mpr (le_antisymm (le_trans haR hRle) h5)
  rw [Work.LWP.BiotSavart.biotSavart_apply, hkey,
    Work.CoreResiduals.BiotSavart.bsField.eq_def]

end Work.CoreResiduals.BiotSavart
