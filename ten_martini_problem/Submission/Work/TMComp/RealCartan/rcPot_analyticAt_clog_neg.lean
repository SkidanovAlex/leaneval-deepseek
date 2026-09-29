import Mathlib

namespace Work.TMComp.RealCartan

open MeasureTheory Set

/-- The logarithmic potential `w ↦ ∫_{t ∈ B} log (t - w)` is analytic at `z`, provided the kernel
`(t:ℂ) - w` stays in the slit plane for `t ∈ B` and `w` close to `z`, and stays a distance `δ > 0`
away from `0`, so that the derivative `-1 / ((t:ℂ) - w)` is uniformly bounded by `1/δ`.

The proof is differentiation under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`): the integrand is holomorphic in `w` (the
branch of `Complex.log` is analytic on the slit plane) with derivative bounded by the integrable
constant `1/δ` on `B`. -/
theorem rcPot_analyticAt_clog_neg {B : Set ℝ} {z : ℂ} {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hBm : MeasurableSet B) (hvol : MeasureTheory.volume B ≠ ⊤)
    (hsep : ∀ t ∈ B, ∀ w ∈ Metric.ball z ρ, δ ≤ ‖w - (t:ℂ)‖)
    (hslit : ∀ t ∈ B, ∀ w ∈ Metric.ball z ρ, ((t:ℂ) - w) ∈ Complex.slitPlane)
    (hint : ∀ w ∈ Metric.ball z ρ, MeasureTheory.Integrable (fun t : ℝ => Complex.log ((t:ℂ) - w)) (MeasureTheory.volume.restrict B)) :
    AnalyticAt ℂ (fun w : ℂ => ∫ t in B, Complex.log ((t:ℂ) - w)) z := by
  have hfin : IsFiniteMeasure (MeasureTheory.volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hvol⟩
  -- Measurability of the integrand in `t`, for every parameter.
  have hmeas : ∀ x : ℂ, AEStronglyMeasurable (fun t : ℝ => Complex.log ((t:ℂ) - x))
      (MeasureTheory.volume.restrict B) := fun x =>
    (Complex.measurable_log.comp
      ((Complex.continuous_ofReal.sub continuous_const).measurable)).aestronglyMeasurable
  have hmeas' : ∀ x : ℂ, AEStronglyMeasurable (fun t : ℝ => (-1 : ℂ) / ((t:ℂ) - x))
      (MeasureTheory.volume.restrict B) := fun x =>
    ((measurable_const.div
      ((Complex.continuous_ofReal.sub continuous_const).measurable)).aestronglyMeasurable)
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [Metric.ball_mem_nhds z hρ] with w hw
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume.restrict B) (𝕜 := ℂ) (E := ℂ)
    (F := fun x : ℂ => fun t : ℝ => Complex.log ((t:ℂ) - x))
    (F' := fun x : ℂ => fun t : ℝ => (-1 : ℂ) / ((t:ℂ) - x))
    (x₀ := w) (s := Metric.ball z ρ) (bound := fun _ : ℝ => 1 / δ)
    (Metric.isOpen_ball.mem_nhds hw)
    (Filter.Eventually.of_forall hmeas)
    (hint w hw)
    (hmeas' w)
    (by
      filter_upwards [MeasureTheory.ae_restrict_mem hBm] with t ht x hx
      have hδt : δ ≤ ‖(t:ℂ) - x‖ := by
        have h := hsep t ht x hx
        rwa [norm_sub_rev] at h
      have hpos : 0 < ‖(t:ℂ) - x‖ := lt_of_lt_of_le hδ hδt
      rw [norm_div, norm_neg, norm_one]
      exact one_div_le_one_div_of_le hδ hδt)
    (MeasureTheory.integrable_const (1 / δ))
    (by
      filter_upwards [MeasureTheory.ae_restrict_mem hBm] with t ht x hx
      have h1 : HasDerivAt (fun y : ℂ => (t:ℂ) - y) (-1) x :=
        (hasDerivAt_id x).const_sub (t:ℂ)
      exact h1.clog (hslit t ht x hx))
  exact key.2.differentiableAt

end Work.TMComp.RealCartan
