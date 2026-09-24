import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup

/-!
# A lower bound for `‖F̂ ψ‖` on the critical range `|y| ≤ 1/2`

The smoothing kernel `ψ = psiSmooth` of GM §9 is `C^∞`, non-negative, even, has integral `1`
and is supported in `[-1/4, 1/4]`.  Since `|2 π x y| ≤ 2 π · (1/4) · (1/2) = π/4` on the
support whenever `|y| ≤ 1/2`, the real part of its Fourier transform is at least
`cos (π/4) = √2/2 ≥ 0` on that range, whence

`‖F̂ ψ y‖ ^ 2 ≥ (√2 / 2) ^ 2 = 1 / 2`   for `|y| ≤ 1 / 2`.

This is exactly the "critical" range in which the Fourier transform of the smoothing kernel
cannot be small; it is used when estimating the `m₃`-sums of GM §9.
-/

open Complex MeasureTheory Filter
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- `ψ = psiSmooth` vanishes outside the ball of radius `1/4`, since its support is the ball of
radius `psiBump.rOut = 1/4`. -/
lemma psiSmooth_zero_of_quarter_le_abs {x : ℝ} (hx : 1 / 4 ≤ |x|) : psiSmooth x = 0 := by
  by_contra h
  have hmem : x ∈ Function.support (psiBump.normed volume) := by
    rw [Function.mem_support]; exact h
  rw [ContDiffBump.support_normed_eq] at hmem
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
  have hr : psiBump.rOut = (1 : ℝ) / 4 := rfl
  linarith [hmem]

/-- The smoothing kernel has compact support. -/
lemma psiSmooth_hcs_quarter : HasCompactSupport psiSmooth :=
  ContDiffBump.hasCompactSupport_normed psiBump (μ := volume)

/-- Pointwise lower bound for the cosine factor: on the support of `ψ` and for `|y| ≤ 1/2`
the phase `2 π v y` lies in `[-π/4, π/4]`, so its cosine is at least `cos (π/4) = √2/2`. -/
lemma psiSmooth_mul_cos_lower_bound {y v : ℝ} (hy : |y| ≤ 1 / 2) :
    psiSmooth v * (Real.sqrt 2 / 2) ≤ psiSmooth v * Real.cos (2 * Real.pi * (v * y)) := by
  rcases eq_or_ne (psiSmooth v) 0 with h | h
  · rw [h, zero_mul, zero_mul]
  · have hv : |v| < 1 / 4 := by
      by_contra hcon
      exact h (psiSmooth_zero_of_quarter_le_abs (not_lt.mp hcon))
    have hθ : |2 * Real.pi * (v * y)| ≤ Real.pi / 4 := by
      have h1 : |2 * Real.pi * (v * y)| = 2 * Real.pi * |v| * |y| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg Real.pi_pos.le]
        ring
      rw [h1]
      have hprod : |v| * |y| ≤ (1 / 4) * (1 / 2) :=
        mul_le_mul hv.le hy (abs_nonneg y) (by norm_num)
      nlinarith [Real.pi_pos, abs_nonneg v, abs_nonneg y]
    have hcos : Real.sqrt 2 / 2 ≤ Real.cos (2 * Real.pi * (v * y)) := by
      have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := |2 * Real.pi * (v * y)|)
        (y := Real.pi / 4) (abs_nonneg _) (by linarith [Real.pi_pos]) hθ
      rwa [Real.cos_abs, Real.cos_pi_div_four] at h
    exact mul_le_mul_of_nonneg_left hcos (psiSmooth_nonneg v)

/-- The real part of `F̂ ψ y` is `∫ v, ψ v * cos (2 π v y)`. -/
lemma Fhat_psiSmooth_re (y : ℝ) :
    (Fhat psiSmooth y).re = ∫ v : ℝ, psiSmooth v * Real.cos (2 * Real.pi * (v * y)) := by
  have hz : Fhat psiSmooth y
      = ∫ v : ℝ, (psiSmooth v : ℂ) *
          Complex.exp ((↑(-2 * Real.pi * (v * y)) : ℂ) * Complex.I) := by
    rw [Fhat, Real.fourier_eq']
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [Real.inner_apply, smul_eq_mul]
    rw [mul_comm]
  have hψintC : Integrable (fun v : ℝ => (psiSmooth v : ℂ)) :=
    (Complex.continuous_ofReal.comp psiSmooth_contDiff.continuous).integrable_of_hasCompactSupport
      (psiSmooth_hcs_quarter.comp_left (by simp))
  have hgint : Integrable (fun v : ℝ => (psiSmooth v : ℂ) *
      Complex.exp ((↑(-2 * Real.pi * (v * y)) : ℂ) * Complex.I)) := by
    refine hψintC.mul_bdd ?_ (c := 1) ?_
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards with v
      rw [Complex.norm_exp_ofReal_mul_I]
  rw [hz]
  change RCLike.re (∫ (v : ℝ), ↑(psiSmooth v) *
      Complex.exp (↑(-2 * Real.pi * (v * y)) * Complex.I))
    = ∫ v : ℝ, psiSmooth v * Real.cos (2 * Real.pi * (v * y))
  rw [← integral_re hgint]
  apply integral_congr_ae
  filter_upwards with v
  have harg : (-2 : ℝ) * Real.pi * (v * y) = -(2 * Real.pi * (v * y)) := by ring
  rw [RCLike.re_eq_complex_re, harg]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg]
  ring

/-- **Lower bound for the Fourier transform of the smoothing kernel on the critical range.**
For `|y| ≤ 1/2` the Fourier transform of `psiSmooth` satisfies `‖F̂ ψ y‖ ^ 2 ≥ 1/2`. -/
theorem psiSmooth_fhat_lower_bound {y : ℝ} (hy : |y| ≤ 1 / 2) :
    1 / 2 ≤ ‖Fhat psiSmooth y‖ ^ 2 := by
  have hψint : Integrable psiSmooth := psiBump.integrable_normed (μ := volume)
  -- Integrability of the two functions compared by `integral_mono`.
  have hInt_cos : Integrable (fun v : ℝ => psiSmooth v * Real.cos (2 * Real.pi * (v * y))) :=
    (psiSmooth_contDiff.continuous.mul
      (Real.continuous_cos.comp (by fun_prop))).integrable_of_hasCompactSupport
      (psiSmooth_hcs_quarter.mul_right)
  have hInt_const : Integrable (fun v : ℝ => psiSmooth v * (Real.sqrt 2 / 2)) :=
    hψint.mul_const _
  have hbound : Real.sqrt 2 / 2 ≤ (Fhat psiSmooth y).re := by
    rw [Fhat_psiSmooth_re]
    calc Real.sqrt 2 / 2 = ∫ v : ℝ, psiSmooth v * (Real.sqrt 2 / 2) := by
          rw [MeasureTheory.integral_mul_const, psiSmooth_integral, one_mul]
      _ ≤ ∫ v : ℝ, psiSmooth v * Real.cos (2 * Real.pi * (v * y)) :=
          integral_mono hInt_const hInt_cos (fun v => psiSmooth_mul_cos_lower_bound hy)
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 / 2 := by positivity
  have hre_nn : 0 ≤ (Fhat psiSmooth y).re := le_trans hnn hbound
  have hsqrt : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  calc (1 : ℝ) / 2 = (Real.sqrt 2 / 2) ^ 2 := hsqrt.symm
    _ ≤ (Fhat psiSmooth y).re ^ 2 := pow_le_pow_left₀ hnn hbound 2
    _ ≤ ‖Fhat psiSmooth y‖ ^ 2 := pow_le_pow_left₀ hre_nn (Complex.re_le_norm _) 2

end

end Work.GM.Affine
