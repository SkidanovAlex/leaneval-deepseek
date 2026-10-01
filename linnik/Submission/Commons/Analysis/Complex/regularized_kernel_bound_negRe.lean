import Mathlib
import Submission.Commons.Analysis.Complex.lapX_regularized_bound_neg
import Submission.Commons.Analysis.Complex.lapX_sub_inv_bound

namespace Commons.Analysis.Complex

open Complex MeasureTheory intervalIntegral Filter Set Topology
open scoped Real Topology BigOperators

set_option autoImplicit false

noncomputable section

/-- The interval Laplace integral `w ↦ ∫_0^{x₀} e^{-wt} f(t) dt` is continuous in `w`, for
`f` continuous on `[0,x₀]`. -/
private lemma continuous_laplace_interval {x₀ : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) :
    Continuous (fun w : ℂ => ∫ t in (0:ℝ)..x₀, Complex.exp (-(w * (t : ℂ))) * f t) := by
  let clip : ℝ → ℝ := fun t => max 0 (min t x₀)
  have hclip : Continuous clip := by unfold clip; fun_prop
  have hmem : ∀ t, clip t ∈ Set.Icc 0 x₀ := by
    intro t; refine ⟨le_max_left _ _, ?_⟩
    exact max_le hx₀.le (min_le_right _ _)
  have hfhat : Continuous (f ∘ clip) := hcont.comp_continuous hclip hmem
  have hfun : Continuous (Function.uncurry (fun (w : ℂ) (t : ℝ) =>
      Complex.exp (-(w * (t : ℂ))) * (f ∘ clip) t)) := by
    have h1 : Continuous (fun p : ℂ × ℝ => Complex.exp (-(p.1 * (p.2 : ℂ)))) :=
      Complex.continuous_exp.comp (((continuous_fst).mul
        (Complex.continuous_ofReal.comp continuous_snd)).neg)
    have h2 : Continuous (fun p : ℂ × ℝ => (f ∘ clip) p.2) := hfhat.comp continuous_snd
    exact h1.mul h2
  have hmain := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hfun (0:ℝ) x₀
  refine hmain.congr (fun w => ?_)
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le hx₀.le] at ht
  show Complex.exp (-(w * (t : ℂ))) * (f ∘ clip) t = Complex.exp (-(w * (t : ℂ))) * f t
  congr 1
  simp only [Function.comp_apply, clip]
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- Bound for the `f(0)`-regularized Laplace kernel `F₀(z) = ∫_0^{x₀} e^{-zt} f t dt - f 0/z`
in the left half-plane `Re z ≤ 0` (where the naive `1/|z|²` bound still holds up to the
exponential factor `e^{|Re z| x₀}`). -/
theorem regularized_kernel_bound_negRe {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {z : ℂ} (hz : z ≠ 0) (hzre : z.re ≤ 0) :
    ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t) - f 0 / z‖
      ≤ Real.exp (|z.re| * x₀) * (5 * B * x₀ + 2 * ‖f 0‖ / x₀) / ‖z‖ ^ 2 := by
  by_cases hlt : z.re < 0
  · -- left open half-plane: use the kernel bound on `Re z < 0`
    have h := lapX_regularized_bound_neg hx₀ hB hcont hf2 hBnd hvan hlt
    have hE1 : (1:ℝ) ≤ Real.exp (-z.re * x₀) := Real.one_le_exp (by nlinarith [hlt, hx₀])
    have hnum : 3 * B * x₀ * Real.exp (-z.re * x₀)
          + ‖f 0‖ * (Real.exp (-z.re * x₀) + 1) / x₀
        ≤ Real.exp (-z.re * x₀) * (5 * B * x₀ + 2 * ‖f 0‖ / x₀) := by
      rw [← sub_nonneg]
      have hkey : Real.exp (-z.re * x₀) * (5 * B * x₀ + 2 * ‖f 0‖ / x₀)
            - (3 * B * x₀ * Real.exp (-z.re * x₀)
                + ‖f 0‖ * (Real.exp (-z.re * x₀) + 1) / x₀)
          = 2 * B * x₀ * Real.exp (-z.re * x₀)
            + ‖f 0‖ * (Real.exp (-z.re * x₀) - 1) / x₀ := by ring
      rw [hkey]
      apply add_nonneg
      · positivity
      · apply div_nonneg
        · exact mul_nonneg (norm_nonneg _) (sub_nonneg.mpr hE1)
        · exact hx₀.le
    calc ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t) - f 0 / z‖
        ≤ (3 * B * x₀ * Real.exp (-z.re * x₀)
            + ‖f 0‖ * (Real.exp (-z.re * x₀) + 1) / x₀) / ‖z‖ ^ 2 := h
      _ ≤ Real.exp (-z.re * x₀) * (5 * B * x₀ + 2 * ‖f 0‖ / x₀) / ‖z‖ ^ 2 :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = Real.exp (|z.re| * x₀) * (5 * B * x₀ + 2 * ‖f 0‖ / x₀) / ‖z‖ ^ 2 := by
          rw [abs_of_neg hlt]
  · -- boundary line `Re z = 0`: limit of the right-half-plane bound
    have hzre0 : z.re = 0 := le_antisymm hzre (not_lt.mp hlt)
    have hIcont : Continuous
        (fun w : ℂ => ∫ t in (0:ℝ)..x₀, Complex.exp (-(w * (t : ℂ))) * f t) :=
      continuous_laplace_interval hx₀ hcont
    have hGcont : ContinuousAt
        (fun w : ℂ => (∫ t in (0:ℝ)..x₀, Complex.exp (-(w * (t : ℂ))) * f t) - f 0 / w) z :=
      ContinuousAt.sub hIcont.continuousAt
        (ContinuousAt.div continuousAt_const continuousAt_id hz)
    have h0 : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))) atTop (nhds (0:ℝ)) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hseq : Tendsto (fun n : ℕ => ((1/((n:ℝ)+1) : ℝ) : ℂ)) atTop (nhds 0) := by
      have h1 := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp h0
      rw [Complex.ofReal_zero] at h1
      exact h1
    let w : ℕ → ℂ := fun n => z + ((1/((n:ℝ)+1) : ℝ) : ℂ)
    have hw : Tendsto w atTop (nhds z) := by
      simpa [w] using tendsto_const_nhds.add hseq
    have hwre : ∀ n : ℕ, (w n).re = 1/((n:ℝ)+1) := by
      intro n; simp only [w, Complex.add_re, Complex.ofReal_re, hzre0, zero_add]
    have hwpos : ∀ n : ℕ, 0 < (w n).re := by
      intro n; rw [hwre n]; positivity
    have hbound : ∀ n : ℕ,
        ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(w n * (t : ℂ))) * f t) - f 0 / (w n)‖
          ≤ (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / ‖w n‖ ^ 2 := by
      intro n
      exact lapX_sub_inv_bound hx₀ hB hcont hf2 hBnd hvan (hwpos n)
    have htendG : Tendsto (fun n : ℕ =>
          ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(w n * (t : ℂ))) * f t) - f 0 / (w n)‖) atTop
        (nhds ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t) - f 0 / z‖) := by
      have h := (hGcont.tendsto.comp hw).norm
      simpa [w, Function.comp_apply] using h
    have hzn2 : (0:ℝ) < ‖z‖ ^ 2 := by
      have : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
      positivity
    have htendR : Tendsto (fun n : ℕ =>
          (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / ‖w n‖ ^ 2) atTop
        (nhds ((3 * B * x₀ + 2 * ‖f 0‖ / x₀) / ‖z‖ ^ 2)) :=
      tendsto_const_nhds.div ((hw.norm).pow 2) (ne_of_gt hzn2)
    have hle : ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t) - f 0 / z‖
        ≤ (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / ‖z‖ ^ 2 :=
      le_of_tendsto_of_tendsto' htendG htendR hbound
    calc ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t) - f 0 / z‖
        ≤ (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / ‖z‖ ^ 2 := hle
      _ ≤ Real.exp (|z.re| * x₀) * (5 * B * x₀ + 2 * ‖f 0‖ / x₀) / ‖z‖ ^ 2 := by
          rw [hzre0, abs_zero, zero_mul, Real.exp_zero, one_mul]
          apply div_le_div_of_nonneg_right _ (le_of_lt hzn2)
          nlinarith [hB, hx₀]

end

end Commons.Analysis.Complex
