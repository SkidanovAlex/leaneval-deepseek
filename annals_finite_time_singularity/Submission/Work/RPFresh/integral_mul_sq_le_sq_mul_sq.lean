import Mathlib.MeasureTheory.Function.L2Space

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped RealInnerProductSpace

namespace Work.RPFresh

/-- Cauchy–Schwarz (Bunyakovsky) inequality for the Lebesgue integral, exponent `2`:
for real functions `f`, `h` with `f²` and `h²` integrable,
`(∫ f h)² ≤ (∫ f²) * (∫ h²)`.

The proof passes to `Lp ℝ 2 μ`, an inner product space whose inner product is the integral
of the pointwise product, applies the abstract Cauchy–Schwarz
`real_inner_mul_inner_self_le`, and transports the four integrals back along the `MemLp.toLp`
a.e.-equalities.  The membership `MemLp f 2 μ` is obtained from the hypotheses through
`MeasureTheory.memLp_two_iff_integrable_sq`. -/
theorem integral_mul_sq_le_sq_mul_sq {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {f h : α → ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable f μ) (hhm : MeasureTheory.AEStronglyMeasurable h μ)
    (hfi : MeasureTheory.Integrable (fun x => f x ^ 2) μ)
    (hhi : MeasureTheory.Integrable (fun x => h x ^ 2) μ) :
    (∫ x, f x * h x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, h x ^ 2 ∂μ) := by
  have hf : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm).2 hfi
  have hh : MemLp h 2 μ := (memLp_two_iff_integrable_sq hhm).2 hhi
  have hB : (∫ x, f x * h x ∂μ) = ∫ x, (hf.toLp f) x * (hh.toLp h) x ∂μ :=
    integral_congr_ae (by
      filter_upwards [hf.coeFn_toLp, hh.coeFn_toLp] with x hx hy
      rw [hx, hy])
  have hA : (∫ x, f x ^ 2 ∂μ) = ∫ x, (hf.toLp f) x * (hf.toLp f) x ∂μ :=
    integral_congr_ae (by
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx, sq])
  have hC : (∫ x, h x ^ 2 ∂μ) = ∫ x, (hh.toLp h) x * (hh.toLp h) x ∂μ :=
    integral_congr_ae (by
      filter_upwards [hh.coeFn_toLp] with x hx
      rw [hx, sq])
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hh.toLp h)
  simp only [L2.inner_def, Real.inner_apply] at h
  rw [hB, hA, hC]
  simpa [sq] using h

end Work.RPFresh
