import Mathlib
import Submission.Work.RHContract.Corpus

namespace Work.RHContract.B

open MeasureTheory Set Filter
open scoped Topology

/-- Norm of the candidate derivative of the Mellin integrand at `z`, for `t > 0`. -/
private lemma norm_deriv_eq (f : ℝ → ℝ) (z : ℂ) {t : ℝ} (ht : 0 < t) (ht1 : 1 ≤ t)
    (hf : 0 ≤ f t) :
    ‖(f t : ℂ) * ((t : ℂ) ^ (-z - 1) * Complex.log (t : ℂ) * (-1))‖
      = f t * t ^ (-z - 1).re * Real.log t := by
  rw [← Complex.ofReal_log ht.le]
  simp only [norm_mul, norm_neg, norm_one, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg ht1), abs_of_nonneg hf]
  ring

/-- Norm bound for the Mellin integrand at `s₀`, dominated by the value at `a₀`. -/
private lemma integrand_norm_le (f : ℝ → ℝ) (a₀ : ℝ) (s₀ : ℂ) (h₀ : a₀ ≤ s₀.re)
    {t : ℝ} (ht1 : 1 ≤ t) (hf : 0 ≤ f t) :
    ‖(f t : ℂ) * (t : ℂ) ^ (-s₀ - 1)‖ ≤ f t * t ^ (-a₀ - 1) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hf]
  refine mul_le_mul_of_nonneg_left ?_ hf
  refine Real.rpow_le_rpow_of_exponent_le ht1 ?_
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  linarith

/-- The uniform bound on the derivative on a small ball, using that `t ^ (-δ) * log t` is
bounded for `δ > 0` and `t ≥ 1`. -/
private lemma deriv_bound (f : ℝ → ℝ) (a₀ : ℝ) (s₀ z : ℂ) {v : ℝ}
    (hv : v = (s₀.re - a₀) / 2) (hv0 : 0 < v) (hz : z ∈ Metric.ball s₀ v)
    {t : ℝ} (ht : 2 < t) (hf : 0 ≤ f t) :
    f t * t ^ (-z - 1).re * Real.log t ≤ (1 / v) * (f t * t ^ (-a₀ - 1)) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hzr : a₀ + v ≤ z.re := by
    have h1 : s₀.re - z.re ≤ ‖z - s₀‖ := by
      have := Complex.re_le_norm (s₀ - z)
      simpa [Complex.sub_re, norm_sub_rev] using this
    rw [Metric.mem_ball, Complex.dist_eq] at hz
    linarith
  have hexp : (-z - 1).re ≤ -a₀ - v - 1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have h2 : t ^ (-a₀ - v - 1) = t ^ (-a₀ - 1) * t ^ (-v) := by
    rw [← Real.rpow_add ht0]; ring_nf
  have h3 : t ^ (-v) * Real.log t ≤ 1 / v := by
    have h4 : Real.log t ≤ t ^ v / v := Real.log_le_rpow_div ht0.le hv0
    calc t ^ (-v) * Real.log t ≤ t ^ (-v) * (t ^ v / v) := by gcongr
      _ = 1 / v := by
        rw [← mul_div_assoc, ← Real.rpow_add ht0, show -v + v = 0 by ring, Real.rpow_zero,
          one_div]
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1
  calc f t * t ^ (-z - 1).re * Real.log t
      ≤ f t * t ^ (-a₀ - v - 1) * Real.log t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 hexp) hf) hlog
      _ = f t * (t ^ (-a₀ - 1) * t ^ (-v)) * Real.log t := by rw [h2]
      _ = (f t * t ^ (-a₀ - 1)) * (t ^ (-v) * Real.log t) := by ring
      _ ≤ (f t * t ^ (-a₀ - 1)) * (1 / v) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hf (Real.rpow_nonneg ht0.le _))
      _ = (1 / v) * (f t * t ^ (-a₀ - 1)) := by ring

theorem mellin_analytic
    (f : ℝ → ℝ) (hzero : ∀ x : ℝ, x < 2 → f x = 0) (hmeas : Measurable f)
    (hnonneg : ∀ x : ℝ, 2 ≤ x → 0 ≤ f x)
    (a₀ : ℝ) (ha₀ : MeasureTheory.IntegrableOn (fun x : ℝ => f x * x ^ (-a₀ - 1)) (Set.Ioi 2)) :
    AnalyticOn ℂ (fun s : ℂ => ∫ x in Set.Ioi 2, (f x : ℂ) * (x : ℂ) ^ (-s - 1))
      {s : ℂ | a₀ < s.re} := by
  have key : ∀ s₀ : ℂ, a₀ < s₀.re → DifferentiableAt ℂ
      (fun s : ℂ => ∫ x in Set.Ioi 2, (f x : ℂ) * (x : ℂ) ^ (-s - 1)) s₀ := by
    intro s₀ h₀
    have hv0 : 0 < (s₀.re - a₀) / 2 := by linarith
    have hmem : Metric.ball s₀ ((s₀.re - a₀) / 2) ∈ 𝓝 s₀ :=
      Metric.ball_mem_nhds s₀ hv0
    have hcont : ∀ z : ℂ, ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-z - 1)) (Set.Ioi 2) := fun z =>
      continuousOn_of_forall_continuousAt fun t ht =>
        Complex.continuousAt_ofReal_cpow_const t (-z - 1)
          (Or.inr (ne_of_gt (by have h2 : (2 : ℝ) < t := ht; linarith)))
    have hF_meas : ∀ᶠ z : ℂ in 𝓝 s₀, AEStronglyMeasurable
        (fun t : ℝ => (f t : ℂ) * (t : ℂ) ^ (-z - 1)) (volume.restrict (Set.Ioi 2)) :=
      Eventually.of_forall fun z => (hmeas.complex_ofReal.aestronglyMeasurable).mul
        ((hcont z).aestronglyMeasurable measurableSet_Ioi)
    have hF_int : Integrable (fun t : ℝ => (f t : ℂ) * (t : ℂ) ^ (-s₀ - 1))
        (volume.restrict (Set.Ioi 2)) := by
      refine Integrable.mono' ha₀ ?_ ?_
      · exact (hmeas.complex_ofReal.aestronglyMeasurable).mul
          ((hcont s₀).aestronglyMeasurable measurableSet_Ioi)
      · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
        have ht2 : (2 : ℝ) < t := ht
        have ht1 : (1 : ℝ) ≤ t := by linarith
        exact integrand_norm_le f a₀ s₀ h₀.le ht1 (hnonneg t (by linarith))
    have hlogmeas : Measurable fun t : ℝ => Complex.log (t : ℂ) :=
      Complex.measurable_log.comp Complex.measurable_ofReal
    have hF'_meas : AEStronglyMeasurable
        (fun t : ℝ => (f t : ℂ) * ((t : ℂ) ^ (-s₀ - 1) * Complex.log (t : ℂ) * (-1)))
        (volume.restrict (Set.Ioi 2)) :=
      (hmeas.complex_ofReal.aestronglyMeasurable).mul
        ((((hcont s₀).aestronglyMeasurable measurableSet_Ioi).mul
          (hlogmeas.aestronglyMeasurable)).mul_const (-1))
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ioi 2)),
        ∀ z ∈ Metric.ball s₀ ((s₀.re - a₀) / 2),
        ‖(f t : ℂ) * ((t : ℂ) ^ (-z - 1) * Complex.log (t : ℂ) * (-1))‖
          ≤ (1 / ((s₀.re - a₀) / 2)) * (f t * t ^ (-a₀ - 1)) := by
      refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht z hz => ?_
      have ht2 : (2 : ℝ) < t := ht
      have ht1 : (1 : ℝ) ≤ t := by linarith
      have ht0 : (0 : ℝ) < t := by linarith
      rw [norm_deriv_eq f z ht0 ht1 (hnonneg t (by linarith))]
      exact deriv_bound f a₀ s₀ z rfl hv0 hz ht2 (hnonneg t (by linarith))
    have hbound_int : Integrable
        (fun t : ℝ => (1 / ((s₀.re - a₀) / 2)) * (f t * t ^ (-a₀ - 1)))
        (volume.restrict (Set.Ioi 2)) := ha₀.const_mul _
    have h_diff : ∀ᵐ t ∂(volume.restrict (Set.Ioi 2)),
        ∀ z ∈ Metric.ball s₀ ((s₀.re - a₀) / 2),
        HasDerivAt (fun z : ℂ => (f t : ℂ) * (t : ℂ) ^ (-z - 1))
          ((f t : ℂ) * ((t : ℂ) ^ (-z - 1) * Complex.log (t : ℂ) * (-1))) z := by
      refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht z hz => ?_
      have ht0 : (0 : ℝ) < t := by have h2 : (2 : ℝ) < t := ht; linarith
      have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)
      have h1 : HasDerivAt (fun z : ℂ => -z - 1) (-1) z := by
        simpa using (hasDerivAt_id' z).neg.sub_const 1
      exact (h1.const_cpow (Or.inl htne)).const_mul ((f t : ℂ))
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi 2))
      (F := fun z t => (f t : ℂ) * (t : ℂ) ^ (-z - 1))
      (F' := fun z t => (f t : ℂ) * ((t : ℂ) ^ (-z - 1) * Complex.log (t : ℂ) * (-1)))
      (bound := fun t => (1 / ((s₀.re - a₀) / 2)) * (f t * t ^ (-a₀ - 1)))
      (x₀ := s₀) (s := Metric.ball s₀ ((s₀.re - a₀) / 2))
      hmem hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2.differentiableAt
  refine DifferentiableOn.analyticOn (fun s hs => (key s hs).differentiableWithinAt) ?_
  exact isOpen_lt continuous_const Complex.continuous_re

end Work.RHContract.B
