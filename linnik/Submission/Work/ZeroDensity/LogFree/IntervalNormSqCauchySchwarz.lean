import Mathlib

namespace Work.ZeroDensity.LogFree

open MeasureTheory

/-- Cauchy–Schwarz for the integral over an interval of the norm of a bounded measurable
complex-valued function. -/
theorem IntervalNormSqCauchySchwarz {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℂ) (M : ℝ)
    (hf : Measurable f) (hfb : ∀ x, ‖f x‖ ≤ M) :
    (∫ x in a..b, ‖f x‖) ^ 2 ≤ (b - a) * ∫ x in a..b, ‖f x‖ ^ 2 := by
  -- Work on the finite measure space `volume.restrict (Ioc a b)` carried by the interval.
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  set μ : Measure ℝ := volume.restrict (Set.Ioc a b) with hμ
  have hfin : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  -- The bounded measurable function `x ↦ ‖f x‖` lies in `L²`, and so does the constant `1`.
  have hfmes : Measurable fun x : ℝ => ‖f x‖ := hf.norm
  have hm1 : MemLp (fun x : ℝ => ‖f x‖) (ENNReal.ofReal 2) μ :=
    MemLp.of_bound hfmes.aestronglyMeasurable (max M 0)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (norm_nonneg (f x))]
        exact le_trans (hfb x) (le_max_left _ _))
  have hm2 : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ := memLp_const 1
  -- Hölder with conjugate exponents `p = q = 2`.
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hold := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun x => norm_nonneg (f x))
    (Filter.Eventually.of_forall fun _ => zero_le_one) hm1 hm2
  simp only [mul_one, Real.rpow_two, one_pow] at hold
  -- The `L¹` norm of the constant `1` is the length `b - a` of the interval.
  have hvol : ∫ x : ℝ, (1 : ℝ) ∂μ = b - a := by
    rw [hμ, ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const]
    simp
  rw [hvol] at hold
  -- Both sides are nonnegative, so we may square the Hölder inequality.
  have hL : 0 ≤ ∫ x : ℝ, ‖f x‖ ∂μ := integral_nonneg fun x => norm_nonneg (f x)
  have hA : 0 ≤ ∫ x : ℝ, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ b - a := sub_nonneg.mpr hab
  have hsq : (∫ x : ℝ, ‖f x‖ ∂μ) ^ 2 ≤
      ((∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * (b - a) ^ ((1 : ℝ) / 2)) ^ 2 :=
    pow_le_pow_left₀ hL hold 2
  calc (∫ x : ℝ, ‖f x‖ ∂μ) ^ 2
      ≤ ((∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * (b - a) ^ ((1 : ℝ) / 2)) ^ 2 := hsq
    _ = (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) * (b - a) := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hA, Real.sq_sqrt hB]
    _ = (b - a) * ∫ x : ℝ, ‖f x‖ ^ 2 ∂μ := by ring

end Work.ZeroDensity.LogFree
