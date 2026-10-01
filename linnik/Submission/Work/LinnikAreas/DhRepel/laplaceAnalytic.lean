import Mathlib

namespace Work.LinnikAreas.DhRepel

open MeasureTheory Set intervalIntegral Complex

/-- The Laplace transform `z ↦ ∫₀^{x₀} exp (-(z * t)) f t dt` of a function continuous on
`[0, x₀]` is entire; in particular it is differentiable on the open right half-plane and
continuous on the closed right half-plane. -/
theorem laplaceAnalytic {x₀ : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀)) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t) {z : ℂ | 0 < z.re} ∧
    ContinuousOn (fun z : ℂ => ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t) {z : ℂ | 0 ≤ z.re} := by
  have hx₀le : (0:ℝ) ≤ x₀ := hx₀.le
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hcontI : ∀ x : ℂ, ContinuousOn (fun t : ℝ => Complex.exp (x * (-(t:ℂ))) * f t) (Set.Icc 0 x₀) := by
    intro x
    refine (Complex.continuous_exp.comp_continuousOn ?_).mul hcont
    fun_prop
  have hcontI' : ∀ x : ℂ, ContinuousOn (fun t : ℝ => Complex.exp (x * (-(t:ℂ))) * (-(t:ℂ)) * f t) (Set.Icc 0 x₀) := by
    intro x
    refine ((Complex.continuous_exp.comp_continuousOn ?_).mul ?_).mul hcont
    · fun_prop
    · fun_prop
  set F : ℂ → ℂ := fun z => ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t:ℂ))) * f t with hF
  -- rewrite `-(z * t)` as `z * (-t)` so that the chain rule applies syntactically
  have hGF : F = (fun z : ℂ => ∫ t in (0:ℝ)..x₀, Complex.exp (z * (-(t:ℂ))) * f t) := by
    funext z
    simp only [hF]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [mul_neg]
  have key : ∀ z : ℂ, HasDerivAt F (∫ t in (0:ℝ)..x₀, Complex.exp (z * (-(t:ℂ))) * (-(t:ℂ)) * f t) z := by
    intro z
    rw [hGF]
    have hle := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0:ℝ)) (b := x₀)
      (bound := fun _ : ℝ => (x₀ + 1) * (C + 1) * Real.exp ((|z.re| + 1) * x₀))
      (F := fun w t => Complex.exp (w * (-(t:ℂ))) * f t)
      (F' := fun w t => Complex.exp (w * (-(t:ℂ))) * (-(t:ℂ)) * f t)
      (x₀ := z) (s := Metric.ball z 1)
      (Metric.ball_mem_nhds z one_pos)
      (by
        refine Filter.Eventually.of_forall (fun x => ?_)
        refine ((hcontI x).mono ?_).aestronglyMeasurable measurableSet_uIoc
        intro t ht
        rw [uIoc_of_le hx₀le] at ht
        exact ⟨ht.1.le, ht.2⟩)
      (by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hx₀le]
        exact hcontI z)
      (by
        refine ((hcontI' z).mono ?_).aestronglyMeasurable measurableSet_uIoc
        intro t ht
        rw [uIoc_of_le hx₀le] at ht
        exact ⟨ht.1.le, ht.2⟩)
      (by
        refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
        rw [uIoc_of_le hx₀le] at ht
        obtain ⟨htpos, htle⟩ := ht
        have hft : ‖f t‖ ≤ C := hC t ⟨htpos.le, htle⟩
        have hnormexp : ‖Complex.exp (x * (-(t:ℂ)))‖ = Real.exp (-(x.re * t)) := by
          rw [Complex.norm_exp]
          congr 1
          simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
          ring
        have hnormt : ‖(-(t:ℂ) : ℂ)‖ = t := by
          rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
        have hxre : -x.re ≤ |z.re| + 1 := by
          have hdist : ‖x - z‖ < 1 := by
            simpa [Metric.mem_ball, dist_eq_norm] using hx
          have h1 : |x.re - z.re| ≤ ‖x - z‖ := by
            simpa [Complex.sub_re] using Complex.abs_re_le_norm (x - z)
          have h2 : -(x.re - z.re) ≤ ‖x - z‖ := le_trans (neg_le_abs _) h1
          have h3 : -(z.re) ≤ |z.re| := neg_le_abs z.re
          linarith
        have hbound_exp : Real.exp (-(x.re * t)) ≤ Real.exp ((|z.re| + 1) * x₀) := by
          rw [Real.exp_le_exp]
          have hB : 0 ≤ |z.re| + 1 := by positivity
          have hmul := mul_le_mul hxre htle htpos.le hB
          nlinarith [hmul]
        simp only [norm_mul, hnormexp, hnormt]
        have hd : 0 ≤ ‖f t‖ := norm_nonneg _
        have hE : 0 ≤ Real.exp ((|z.re| + 1) * x₀) := (Real.exp_pos _).le
        have hC1 : 0 ≤ C + 1 := by linarith [le_trans (norm_nonneg (f 0)) (hC 0 ⟨le_refl 0, hx₀le⟩)]
        have htle1 : t ≤ x₀ + 1 := by linarith
        have hft1 : ‖f t‖ ≤ C + 1 := by linarith
        calc Real.exp (-(x.re * t)) * t * ‖f t‖
            ≤ Real.exp ((|z.re| + 1) * x₀) * t * ‖f t‖ := by
              apply mul_le_mul_of_nonneg_right _ hd
              exact mul_le_mul_of_nonneg_right hbound_exp htpos.le
          _ ≤ Real.exp ((|z.re| + 1) * x₀) * (x₀ + 1) * ‖f t‖ := by
              apply mul_le_mul_of_nonneg_right _ hd
              exact mul_le_mul_of_nonneg_left htle1 hE
          _ ≤ Real.exp ((|z.re| + 1) * x₀) * (x₀ + 1) * (C + 1) := by
              exact mul_le_mul_of_nonneg_left hft1 (mul_nonneg hE (by linarith))
          _ = (x₀ + 1) * (C + 1) * Real.exp ((|z.re| + 1) * x₀) := by ring)
      (by
        exact intervalIntegrable_const)
      (by
        refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
        have h1 : HasDerivAt (fun w : ℂ => w * (-(t:ℂ))) (-(t:ℂ)) x := by
          simpa using (hasDerivAt_id x).mul_const (-(t:ℂ))
        exact (h1.cexp).mul_const (f t))
    exact hle.2
  have hdiff : Differentiable ℂ F := fun z => (key z).differentiableAt
  exact ⟨hdiff.differentiableOn, hdiff.continuous.continuousOn⟩

end Work.LinnikAreas.DhRepel
