import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.dslope_analytic_factor
import Submission.Work.Holonomy3.jensen_mean_ineq
import Submission.Work.Holonomy3.circleAverage_log_norm_tendsto

namespace Work.Holonomy3

open MeasureTheory Filter Topology
open scoped Real
open Submission.CDTPlan

/-- The circle average over the unit circle, written as an integral over `[0,1]` against the
parametrisation `t ↦ e^{2πit}`. -/
lemma circleAverage_zero_one_eq_integral (f : ℂ → ℝ) :
    Real.circleAverage f 0 1
      = ∫ t in (0 : ℝ)..1, f (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) := by
  rw [Real.circleAverage_def]
  have hmap : ∀ θ : ℝ, circleMap (0 : ℂ) 1 θ = Complex.exp ((θ : ℂ) * Complex.I) :=
    fun θ => by simp [circleMap]
  simp only [hmap]
  have key := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (c := 2 * Real.pi)
    (fun θ : ℝ => f (Complex.exp ((θ : ℂ) * Complex.I))) (by positivity)
  rw [mul_zero, mul_one] at key
  rw [← key]
  apply intervalIntegral.integral_congr
  intro t _
  push_cast
  ring_nf

/-- The unit-circle parametrisation has norm one. -/
lemma norm_exp_two_pi_I (t : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
  have harg : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)
      = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.norm_exp_ofReal_mul_I]

/-- **Jensen's formula for the conformal size.** For an admissible conformal map `φ` (continuous on
the closed unit disc, holomorphic inside, `φ 0 = 0`, `φ'(0) ≠ 0`), the mean of `log|φ|` over the unit
circle is at least `log|φ'(0)|`. This is the `m = 1` case of the fine holonomy bound, and the reason
the rearrangement integral of the paper dominates `log|φ'(0)|`. -/
theorem circleLog_average_ge (φ : ℂ → ℂ) (hφ : Submission.CDTPlan.AdmissibleMap φ)
    (hφ0 : 0 < ‖deriv φ 0‖) :
    Real.log ‖deriv φ 0‖ ≤ ∫ t in (0 : ℝ)..1, Submission.CDTPlan.circleLog φ t := by
  obtain ⟨hcont, hdiff, hφz0, hnz⟩ := hφ
  obtain ⟨han, hfac⟩ := dslope_analytic_factor φ hdiff hφz0
  -- `dslope φ 0` is the quotient `z ↦ φ z / z`; it satisfies `φ z = z * dslope φ 0 z`.
  have hg0ne : dslope φ 0 0 ≠ 0 := by
    rw [dslope_same]
    exact norm_ne_zero_iff.mp (ne_of_gt hφ0)
  -- continuity of `dslope φ 0` on the closed disc
  have hgcont : ContinuousOn (dslope φ 0) (Metric.closedBall 0 1) := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact (han 0 (by simp [Metric.mem_ball])).continuousAt.continuousWithinAt
    · exact (continuousWithinAt_dslope_of_ne (f := φ) (a := 0) hz0).mpr (hcont z hz)
  -- `dslope φ 0` does not vanish on the unit circle
  have hgne : ∀ z : ℂ, ‖z‖ = 1 → dslope φ 0 z ≠ 0 := by
    intro z hz hgz
    have h := hfac z
    rw [hgz, mul_zero] at h
    exact (hnz z hz) h
  -- Jensen's mean value inequality at every radius `r < 1`
  have hkey : ∀ r : ℝ, 0 < r → r < 1 →
      Real.log ‖deriv φ 0‖ ≤ Real.circleAverage (fun z => Real.log ‖dslope φ 0 z‖) 0 r := by
    intro r hr0 hr1
    have han' : AnalyticOnNhd ℂ (dslope φ 0) (Metric.closedBall 0 r) :=
      han.mono (Metric.closedBall_subset_ball hr1)
    have h := jensen_mean_ineq (dslope φ 0) r hr0 han' hg0ne
    simpa using h
  -- pass to the limit `r → 1⁻`
  have htend := circleAverage_log_norm_tendsto (dslope φ 0) hgcont hgne
  have hmain : Real.log ‖deriv φ 0‖
      ≤ Real.circleAverage (fun z => Real.log ‖dslope φ 0 z‖) 0 1 := by
    refine ge_of_tendsto htend ?_
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[Set.Iio (1 : ℝ)] 1 := by
      rw [Metric.mem_nhdsWithin_iff]
      refine ⟨1 / 2, by norm_num, ?_⟩
      intro x hx
      obtain ⟨hxball, hxio⟩ := hx
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hxball
      exact ⟨by linarith [hxball.1], hxio⟩
    filter_upwards [hmem] with r hr
    exact hkey r hr.1 hr.2
  -- identify the target integral with the circle average
  have hgoal : (∫ t in (0 : ℝ)..1, Submission.CDTPlan.circleLog φ t)
      = Real.circleAverage (fun z => Real.log ‖dslope φ 0 z‖) 0 1 := by
    rw [circleAverage_zero_one_eq_integral (fun z => Real.log ‖dslope φ 0 z‖)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Submission.CDTPlan.circleLog]
    rw [hfac (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))), norm_mul,
      norm_exp_two_pi_I t, one_mul]
  rw [hgoal]
  exact hmain

end Work.Holonomy3
