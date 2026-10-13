import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open MeasureTheory Filter

/-- `L²`-Minkowski (equivalently Cauchy–Schwarz / convexity of the square root) for nonnegative
functions: if `a`, `b ≥ 0` are a.e.-strongly measurable with square-integrable squares, then
`∫ (a + b)² ≤ (√(∫ a²) + √(∫ b²))²`.

Proof: expand the square, estimate the cross term `∫ a b` by Cauchy–Schwarz/Hölder with
conjugate exponents `p = q = 2`, and observe that the resulting right-hand side is the expansion
of `(√(∫ a²) + √(∫ b²))²`. -/
theorem integral_sq_add_le {μ : MeasureTheory.Measure ℝ} {a b : ℝ → ℝ}
    (han : ∀ x, 0 ≤ a x) (hbn : ∀ x, 0 ≤ b x)
    (ha : MeasureTheory.AEStronglyMeasurable a μ)
    (hb : MeasureTheory.AEStronglyMeasurable b μ)
    (h2a : MeasureTheory.Integrable (fun x => a x ^ 2) μ)
    (h2b : MeasureTheory.Integrable (fun x => b x ^ 2) μ) :
    (∫ x, (a x + b x) ^ 2 ∂μ)
      ≤ (Real.sqrt (∫ x, a x ^ 2 ∂μ) + Real.sqrt (∫ x, b x ^ 2 ∂μ)) ^ 2 := by
  have hA0 : 0 ≤ ∫ x, a x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (a x)
  have hB0 : 0 ≤ ∫ x, b x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (b x)
  have hmA : MemLp a (ENNReal.ofReal (2 : ℝ)) μ := by
    rw [ENNReal.ofReal_ofNat]; exact (memLp_two_iff_integrable_sq ha).2 h2a
  have hmB : MemLp b (ENNReal.ofReal (2 : ℝ)) μ := by
    rw [ENNReal.ofReal_ofNat]; exact (memLp_two_iff_integrable_sq hb).2 h2b
  -- the product `a * b` is integrable, by `|a b| ≤ (a² + b²)/2`
  have h2ab : Integrable (fun x => a x * b x) μ := by
    refine ((h2a.add h2b).div_const 2).mono' (ha.mul hb) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    show |a x| * |b x| ≤ (a x ^ 2 + b x ^ 2) / 2
    nlinarith [sq_nonneg (|a x| - |b x|), sq_abs (a x), sq_abs (b x)]
  -- Cauchy–Schwarz for the cross term
  have hCS : ∫ x, a x * b x ∂μ
      ≤ Real.sqrt (∫ x, a x ^ 2 ∂μ) * Real.sqrt (∫ x, b x ^ 2 ∂μ) := by
    have hpq : (2 : ℝ).HolderConjugate 2 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
        (Filter.Eventually.of_forall han) (Filter.Eventually.of_forall hbn) hmA hmB
    simpa [Real.sqrt_eq_rpow] using h
  -- expansion of the square
  have h2ab2 : Integrable (fun x => 2 * (a x * b x)) μ := by
    simpa only [smul_eq_mul] using h2ab.const_mul (2 : ℝ)
  have e0 : ∫ x, (a x + b x) ^ 2 ∂μ = ∫ x, a x ^ 2 + 2 * (a x * b x) + b x ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have e1 : ∫ x, a x ^ 2 + 2 * (a x * b x) ∂μ
      = (∫ x, a x ^ 2 ∂μ) + (∫ x, 2 * (a x * b x) ∂μ) := integral_add h2a h2ab2
  have e2 : ∫ x, a x ^ 2 + 2 * (a x * b x) + b x ^ 2 ∂μ
      = (∫ x, a x ^ 2 + 2 * (a x * b x) ∂μ) + (∫ x, b x ^ 2 ∂μ) :=
    integral_add (h2a.add h2ab2) h2b
  have e3 : (∫ x, 2 * (a x * b x) ∂μ) = 2 * (∫ x, a x * b x ∂μ) :=
    integral_const_mul 2 (fun x => a x * b x)
  have hexp : ∫ x, (a x + b x) ^ 2 ∂μ
      = (∫ x, a x ^ 2 ∂μ) + 2 * (∫ x, a x * b x ∂μ) + (∫ x, b x ^ 2 ∂μ) := by
    rw [e0, e2, e1, e3]
  have hsq : (Real.sqrt (∫ x, a x ^ 2 ∂μ) + Real.sqrt (∫ x, b x ^ 2 ∂μ)) ^ 2
      = (∫ x, a x ^ 2 ∂μ)
        + 2 * (Real.sqrt (∫ x, a x ^ 2 ∂μ) * Real.sqrt (∫ x, b x ^ 2 ∂μ))
        + (∫ x, b x ^ 2 ∂μ) := by
    rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    ring
  rw [hexp, hsq]
  nlinarith [hCS]

end Work.FTS.StrongEps.EpsE4Thr
