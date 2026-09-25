import Mathlib

namespace Work.NN.Core.Value

open MeasureTheory ENNReal
open scoped ENNReal

/-- Interpolation (Lyapunov / Riesz–Thorin convexity) of the `L^p` integral for a single
`ℝ≥0∞`-valued function, in the un-normalised `lintegral` form: if
`1/r = (1-θ)/p + θ/q` with `p, q, r > 0` and `0 < θ < 1`, then
`∫ u^r ≤ (∫ u^p)^(r(1-θ)/p) * (∫ u^q)^(rθ/q)`.

This follows from Hölder's inequality applied to the two functions `u^(r(1-θ))` and
`u^(rθ)` with conjugate exponents `p/(r(1-θ))` and `q/(rθ)`. -/
private theorem lintegral_rpow_interp {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {u : α → ℝ≥0∞} (hu : AEMeasurable u μ)
    {p q r θ : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hint : 1 / r = (1 - θ) / p + θ / q) :
    (∫⁻ a, u a ^ r ∂μ) ≤ (∫⁻ a, u a ^ p ∂μ) ^ (r * (1 - θ) / p) *
        (∫⁻ a, u a ^ q ∂μ) ^ (r * θ / q) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hA : 0 < r * (1 - θ) := mul_pos hr h1θ
  have hB : 0 < r * θ := mul_pos hr hθ0
  have hs : 0 < p / (r * (1 - θ)) := div_pos hp hA
  have ht : 0 < q / (r * θ) := div_pos hq hB
  -- The two exponents `p/(r(1-θ))` and `q/(rθ)` are Hölder conjugate.
  have hinv : (p / (r * (1 - θ)))⁻¹ + (q / (r * θ))⁻¹ = 1 := by
    rw [inv_div, inv_div, mul_div_assoc, mul_div_assoc, ← mul_add, hint.symm, one_div]
    exact mul_inv_cancel₀ hr.ne'
  have hconj : (p / (r * (1 - θ))).HolderConjugate (q / (r * θ)) := by
    refine ⟨?_, hs, ht⟩
    simpa using hinv
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
      (hu.pow_const (r * (1 - θ))) (hu.pow_const (r * θ))
  simp only [Pi.mul_apply] at hholder
  -- `u^(r(1-θ)) * u^(rθ) = u^r`.
  have hL : (∫⁻ a, u a ^ (r * (1 - θ)) * u a ^ (r * θ) ∂μ) = ∫⁻ a, u a ^ r ∂μ := by
    apply lintegral_congr; intro a
    rw [← ENNReal.rpow_add_of_nonneg (r * (1 - θ)) (r * θ) hA.le hB.le]
    congr 1; ring
  -- `(u^(r(1-θ)))^(p/(r(1-θ))) = u^p` and `(u^(rθ))^(q/(rθ)) = u^q`.
  have hR1 : (∫⁻ a, (u a ^ (r * (1 - θ))) ^ (p / (r * (1 - θ))) ∂μ) = ∫⁻ a, u a ^ p ∂μ := by
    apply lintegral_congr; intro a
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  have hR2 : (∫⁻ a, (u a ^ (r * θ)) ^ (q / (r * θ)) ∂μ) = ∫⁻ a, u a ^ q ∂μ := by
    apply lintegral_congr; intro a
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  rw [hL, hR1, hR2] at hholder
  rw [show 1 / (p / (r * (1 - θ))) = r * (1 - θ) / p by field_simp,
      show 1 / (q / (r * θ)) = r * θ / q by field_simp] at hholder
  exact hholder

theorem eLpNorm_interp {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f : α → ℂ} (hf : MeasureTheory.AEStronglyMeasurable f μ)
    {p q r θ : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hint : 1 / r = (1 - θ) / p + θ / q) :
    MeasureTheory.eLpNorm f (ENNReal.ofReal r) μ
      ≤ ENNReal.rpow (MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ) (1 - θ) *
        ENNReal.rpow (MeasureTheory.eLpNorm f (ENNReal.ofReal q) μ) θ := by
  -- Reduce everything to the `lintegral` form.
  have hcore := lintegral_rpow_interp (μ := μ) (u := fun a => ‖f a‖ₑ) hf.enorm
    hp hq hr hθ0 hθ1 hint
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top hf,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top hf,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top hf,
      ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le]
  -- Raise the un-normalised inequality to the power `1/r` and simplify the exponents.
  have step := ENNReal.rpow_le_rpow hcore (by positivity : (0:ℝ) ≤ 1 / r)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1/r)] at step
  simp only [← ENNReal.rpow_mul] at step
  rw [show (r * (1 - θ) / p) * (1 / r) = (1 / p) * (1 - θ) by field_simp,
      show (r * θ / q) * (1 / r) = (1 / q) * θ by field_simp] at step
  simp only [ENNReal.rpow_mul] at step
  exact step

end Work.NN.Core.Value
