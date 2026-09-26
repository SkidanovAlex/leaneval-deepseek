import Mathlib
import Submission.Work.CKFinal.LineDecay.LamDefs

namespace Work.CKFinal.LineDecay

open MeasureTheory Filter

/-- The Laplace-type transform `z ↦ ∫_a^b f t e^{-zt} dt` of a bounded measurable function on a finite interval is entire.  Proof by dominated convergence: for `z` in a ball around `z₀` the derivative integrand `-t f t e^{-zt}` is dominated by `max(|a|,|b|) * B * e^{|t| * (|z₀| + r)}`-type constants, which are integrable on the finite interval. -/
theorem laplace_analytic_compact {f : ℝ → ℂ} {a b B : ℝ} (hB : 0 ≤ B)
    (hf : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (hbound : ∀ t ∈ Set.uIoc a b, ‖f t‖ ≤ B) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∫ t in a..b, f t * Complex.exp (-(z * t))) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  intro z₀
  -- The whole interval lies inside `[-max |a| |b|, max |a| |b|]`.
  have ht_le_max : ∀ t ∈ Set.uIoc a b, |t| ≤ max |a| |b| := by
    intro t ht
    rw [Set.uIoc, Set.mem_Ioc] at ht
    obtain ⟨ht1, ht2⟩ := ht
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h1 : -max |a| |b| ≤ min a b := by
        apply le_min <;>
          linarith [neg_abs_le a, neg_abs_le b, le_max_left |a| |b|, le_max_right |a| |b|]
      linarith
    · have h2 : max a b ≤ max |a| |b| := by
        apply max_le <;>
          linarith [le_abs_self a, le_abs_self b, le_max_left |a| |b|, le_max_right |a| |b|]
      linarith
  set M : ℝ := max |a| |b| with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact le_trans (abs_nonneg a) (le_max_left _ _)
  have ht_le : ∀ t ∈ Set.uIoc a b, |t| ≤ M := fun t ht => by rw [hMdef]; exact ht_le_max t ht
  -- The phase factor is entire in `z`, uniformly in `t`.
  have hcont_exp : ∀ c : ℂ, Continuous (fun t : ℝ => Complex.exp (-(c * (t : ℂ)))) := fun c =>
    Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg)
  have hmeas_f : ∀ c : ℂ, AEStronglyMeasurable (fun t : ℝ => f t * Complex.exp (-(c * (t:ℂ))))
      (volume.restrict (Set.uIoc a b)) := fun c => hf.mul (hcont_exp c).aestronglyMeasurable
  -- Pointwise derivative of the integrand.
  have hderiv : ∀ (t : ℝ) (x : ℂ),
      HasDerivAt (fun z : ℂ => f t * Complex.exp (-(z * (t:ℂ))))
        (f t * (-(t:ℂ)) * Complex.exp (-(x * (t:ℂ)))) x := by
    intro t x
    have h1 : HasDerivAt (fun z : ℂ => z * (t:ℂ)) (t:ℂ) x := by
      simpa using (hasDerivAt_id x).mul_const (t:ℂ)
    have h2 : HasDerivAt (fun z : ℂ => -(z * (t:ℂ))) (-(t:ℂ)) x := h1.neg
    have h3 : HasDerivAt (fun z : ℂ => Complex.exp (-(z * (t:ℂ))))
        (Complex.exp (-(x * (t:ℂ))) * (-(t:ℂ))) x := h2.cexp
    have h4 := h3.const_mul (f t)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h4
  -- Two constants dominating the integrand and its derivative on the ball around `z₀`.
  set C : ℝ := B * M * Real.exp ((‖z₀‖ + 1) * M) with hCdef
  set C₁ : ℝ := B * Real.exp (‖z₀‖ * M) with hC₁def
  have hnorm_bound : ∀ x ∈ Metric.ball z₀ 1, ∀ t ∈ Set.uIoc a b,
      ‖f t * (-(t:ℂ)) * Complex.exp (-(x * (t:ℂ)))‖ ≤ C := by
    intro x hx t ht
    rw [hCdef]
    have hx1 : ‖x‖ ≤ ‖z₀‖ + 1 := by
      have hxd : ‖x - z₀‖ < 1 := by
        rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx
      calc ‖x‖ = ‖(x - z₀) + z₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ 1 + ‖z₀‖ := by linarith
        _ = ‖z₀‖ + 1 := by ring
    have hexp : Real.exp (-(x.re * t)) ≤ Real.exp ((‖z₀‖ + 1) * M) := by
      apply Real.exp_le_exp.mpr
      have h1 : -(x.re * t) ≤ |x.re * t| := neg_le_abs _
      have h2 : |x.re * t| = |x.re| * |t| := abs_mul _ _
      have h3 : |x.re| ≤ ‖x‖ := Complex.abs_re_le_norm x
      have h4 : |x.re| * |t| ≤ ‖x‖ * M := by
        apply mul_le_mul h3 (ht_le t ht) (abs_nonneg _) (norm_nonneg _)
      have h5 : ‖x‖ * M ≤ (‖z₀‖ + 1) * M := by
        apply mul_le_mul_of_nonneg_right hx1 hMnn
      linarith [h1, h2 ▸ h4, h5]
    rw [norm_mul, norm_mul, norm_neg]
    have hnorm : ‖(t:ℂ)‖ = |t| := by simp
    rw [hnorm, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hexp' : 0 ≤ Real.exp (-(x.re * t)) := Real.exp_nonneg _
    calc ‖f t‖ * |t| * Real.exp (-(x.re * t))
        ≤ B * M * Real.exp (-(x.re * t)) := by
          apply mul_le_mul (mul_le_mul (hbound t ht) (ht_le t ht) (abs_nonneg t) hB) (le_refl _)
            hexp' (by positivity)
        _ ≤ B * M * Real.exp ((‖z₀‖ + 1) * M) := by
          apply mul_le_mul (le_refl _) hexp (Real.exp_nonneg _) (by positivity)
  -- Measurability of the derivative integrand at `z₀`.
  have hmeas_f' : AEStronglyMeasurable
      (fun t : ℝ => f t * (-(t:ℂ)) * Complex.exp (-(z₀ * (t:ℂ))))
      (volume.restrict (Set.uIoc a b)) := by
    have hcont : Continuous (fun t : ℝ => (-(t:ℂ)) * Complex.exp (-(z₀ * (t:ℂ)))) :=
      (Complex.continuous_ofReal.neg).mul (hcont_exp z₀)
    have haux : AEStronglyMeasurable (fun t : ℝ => f t * ((-(t:ℂ)) * Complex.exp (-(z₀ * (t:ℂ)))))
        (volume.restrict (Set.uIoc a b)) := hf.mul hcont.aestronglyMeasurable
    simpa only [mul_assoc] using haux
  -- Integrability of the integrand at `z₀` (bounded on a finite interval).
  have hF_int : IntervalIntegrable (fun t : ℝ => f t * Complex.exp (-(z₀ * (t:ℂ)))) volume a b := by
    rw [intervalIntegrable_iff]
    refine MeasureTheory.IntegrableOn.of_bound (μ := volume) (s := Set.uIoc a b) ?_ ?_ C₁ ?_
    · rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
    · exact hmeas_f z₀
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
      rw [hC₁def, norm_mul, Complex.norm_exp]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      have hexp : Real.exp (-(z₀.re * t)) ≤ Real.exp (‖z₀‖ * M) := by
        apply Real.exp_le_exp.mpr
        calc -(z₀.re * t) ≤ |z₀.re * t| := neg_le_abs _
          _ = |z₀.re| * |t| := abs_mul _ _
          _ ≤ ‖z₀‖ * M :=
              mul_le_mul (Complex.abs_re_le_norm z₀) (ht_le t ht) (abs_nonneg _) (norm_nonneg _)
      calc ‖f t‖ * Real.exp (-(z₀.re * t))
          ≤ B * Real.exp (-(z₀.re * t)) :=
            mul_le_mul (hbound t ht) (le_refl _) (Real.exp_nonneg _) hB
        _ ≤ B * Real.exp (‖z₀‖ * M) :=
            mul_le_mul (le_refl _) hexp (Real.exp_nonneg _) hB
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C) volume a b := intervalIntegrable_const
  -- Differentiate under the integral sign.
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b) (x₀ := z₀) (s := Metric.ball z₀ 1)
    (F := fun (z : ℂ) (t : ℝ) => f t * Complex.exp (-(z * (t:ℂ))))
    (F' := fun (z : ℂ) (t : ℝ) => f t * (-(t:ℂ)) * Complex.exp (-(z * (t:ℂ))))
    (bound := fun _ : ℝ => C)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall hmeas_f)
    hF_int
    hmeas_f'
    (Filter.Eventually.of_forall (fun t ht x hx => hnorm_bound x hx t ht))
    hbound_int
    (Filter.Eventually.of_forall (fun t _ x _ => hderiv t x))
  exact key.2.differentiableAt

end Work.CKFinal.LineDecay
