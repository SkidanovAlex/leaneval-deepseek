import Mathlib
import Submission.Work.TMComp.RealCartanDefs

/-!
# The mean value inequality for `‖f‖ * exp (-(c * h))`

If `h : ℂ → ℝ` is harmonic on an open set `U`, `f : ℂ → ℂ` is holomorphic on `U`, and the
closed disc `closedBall z r` is contained in `U`, then

`‖f z‖ * exp (-(c * h z)) ≤ circleAverage (fun ζ => ‖f ζ‖ * exp (-(c * h ζ))) z r`.

The function `ζ ↦ ‖f ζ‖ * exp (-(c * h ζ))` is (locally) the modulus of a holomorphic function:
on a ball around `z` inside `U`, the harmonic function `h` is the real part of a holomorphic
function `F`, so that `‖f ζ‖ * exp (-(c * h ζ)) = ‖f ζ * exp (-c * F ζ)‖` there.  The mean value
property for holomorphic functions then gives the assertion.
-/

set_option linter.unusedVariables false

open Metric Set

namespace Work.TMComp.RealCartan

theorem rcMeanValue {U : Set ℂ} (hU : IsOpen U) {h : ℂ → ℝ} (hh : InnerProductSpace.HarmonicOnNhd h U)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (c : ℝ) {z : ℂ} (hz : z ∈ U) (hzf : f z ≠ 0)
    {r : ℝ} (hr : 0 < r) (hrU : Metric.closedBall z r ⊆ U) :
    ‖f z‖ * Real.exp (-(c * h z)) ≤
      Real.circleAverage (fun ζ => ‖f ζ‖ * Real.exp (-(c * h ζ))) z r := by
  -- A slightly larger ball around `z` on which `h` is harmonic and `f` is holomorphic.
  obtain ⟨δ, hδpos, hδU⟩ := (isCompact_closedBall z r).exists_thickening_subset_open hU hrU
  rw [thickening_closedBall hδpos hr.le z] at hδU
  have hRdef : r < δ + r := by linarith
  have hRpos : 0 < δ + r := by linarith
  -- `h` is the real part of a holomorphic function `F` on that ball.
  obtain ⟨F, hFana, hFre⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (hh.mono hδU)
  let Φ : ℂ → ℂ := fun ζ => f ζ * Complex.exp (((-c : ℝ) : ℂ) * F ζ)
  have hfana : AnalyticOnNhd ℂ f (ball z (δ + r)) := hf.mono hδU
  have hΦana : AnalyticOnNhd ℂ Φ (ball z (δ + r)) := by
    apply hfana.mul
    exact (((analyticOnNhd_const (v := ((-c : ℝ) : ℂ))).mul hFana).cexp)
  -- `‖Φ‖` agrees with the function whose circle average we are bounding.
  have hval : ∀ ζ ∈ ball z (δ + r), ‖Φ ζ‖ = ‖f ζ‖ * Real.exp (-(c * h ζ)) := by
    intro ζ hζ
    have hFζ : (F ζ).re = h ζ := hFre hζ
    simp only [Φ, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
    rw [hFζ, show (-c) * h ζ = -(c * h ζ) by ring]
  have hdiff : DiffContOnCl ℂ Φ (ball z |r|) := by
    rw [abs_of_pos hr]
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z (ne_of_gt hr)]
    exact hΦana.differentiableOn.mono (closedBall_subset_ball hRdef)
  have hMV : Real.circleAverage Φ z r = Φ z := hdiff.circleAverage
  -- Norm of a circle average is at most the circle average of the norm.
  have hnorm : ‖Real.circleAverage Φ z r‖ ≤ Real.circleAverage (fun ζ => ‖Φ ζ‖) z r := by
    rw [Real.circleAverage_def, Real.circleAverage_def]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi))]
    rw [smul_eq_mul]
    exact mul_le_mul_of_nonneg_left
      (intervalIntegral.norm_integral_le_integral_norm (by positivity : (0 : ℝ) ≤ 2 * Real.pi))
      (by positivity)
  have hcongr : Real.circleAverage (fun ζ => ‖Φ ζ‖) z r =
      Real.circleAverage (fun ζ => ‖f ζ‖ * Real.exp (-(c * h ζ))) z r := by
    apply Real.circleAverage_congr_sphere
    intro ζ hζ
    rw [abs_of_pos hr] at hζ
    exact hval ζ (sphere_subset_ball hRdef hζ)
  calc ‖f z‖ * Real.exp (-(c * h z)) = ‖Φ z‖ := (hval z (mem_ball_self hRpos)).symm
    _ = ‖Real.circleAverage Φ z r‖ := by rw [hMV]
    _ ≤ Real.circleAverage (fun ζ => ‖Φ ζ‖) z r := hnorm
    _ = Real.circleAverage (fun ζ => ‖f ζ‖ * Real.exp (-(c * h ζ))) z r := hcongr

end Work.TMComp.RealCartan
