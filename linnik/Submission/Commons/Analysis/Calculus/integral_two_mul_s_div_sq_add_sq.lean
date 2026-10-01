import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory

namespace Commons.Analysis.Calculus

theorem integral_two_mul_s_div_sq_add_sq {s : ℝ} (hs : 0 < s) (δ : ℝ) :
    ∫ u in (-δ)..δ, (2 * s) / (u ^ 2 + s ^ 2) = 4 * Real.arctan (δ / s) := by
  have hsq : ∀ u : ℝ, u ^ 2 + s ^ 2 ≠ 0 := by
    intro u
    have : 0 < u ^ 2 + s ^ 2 := by positivity
    exact ne_of_gt this
  have hderiv : ∀ u : ℝ, HasDerivAt (fun u : ℝ => 2 * Real.arctan (u / s))
      (2 * s / (u ^ 2 + s ^ 2)) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => u / s) (1 / s) u := by
      simpa using (hasDerivAt_id u).div_const s
    have h2 : HasDerivAt (fun u : ℝ => Real.arctan (u / s))
        (1 / (1 + (u / s) ^ 2) * (1 / s)) u := h1.arctan
    have h3 := h2.const_mul 2
    refine h3.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun u : ℝ => (2 * s) / (u ^ 2 + s ^ 2)) volume (-δ) δ := by
    apply Continuous.intervalIntegrable
    exact continuous_const.div (by fun_prop) (fun u => hsq u)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint]
  rw [show -δ / s = -(δ / s) by ring, Real.arctan_neg]
  ring

end Commons.Analysis.Calculus