import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Commons.Analysis.Integral

open MeasureTheory Real Set Filter

set_option maxHeartbeats 800000

/-- Algebraic rewrite: for `x > √2` the difference of the two inverse square roots
equals a single fraction with denominator `x √(x²-1) (x + √(x²-1))`. -/
private lemma eq_div_of_sqrt_sub_one {x : ℝ} (hx : Real.sqrt 2 < x) :
    ((Real.sqrt (x^2-1))⁻¹ - x⁻¹) * Real.sqrt x
      = Real.sqrt x / (x * Real.sqrt (x^2-1) * (x + Real.sqrt (x^2-1))) := by
  have hxpos : 0 < x := by
    have h1 : (1:ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two; linarith
  have hx21 : 0 < x^2 - 1 := by
    have h2 : (2:ℝ) < x^2 := by
      have hsq : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2, hx, hsq]
    linarith
  have hs2 : (Real.sqrt (x^2-1))^2 = x^2 - 1 := Real.sq_sqrt (le_of_lt hx21)
  have hspos : 0 < Real.sqrt (x^2-1) := by rw [Real.sqrt_pos]; exact hx21
  have key : ((Real.sqrt (x^2-1))⁻¹ - x⁻¹) =
      (x * Real.sqrt (x^2-1) * (x + Real.sqrt (x^2-1)))⁻¹ := by
    have hxs : x - Real.sqrt (x^2-1) = (x + Real.sqrt (x^2-1))⁻¹ :=
      eq_inv_of_mul_eq_one_right (by nlinarith [hs2])
    rw [inv_sub_inv (by exact ne_of_gt hspos) (by exact ne_of_gt hxpos), hxs]
    field_simp
  rw [key, inv_mul_eq_div]

/-- Pointwise bound: on `(√2, ∞)` the integrand is nonnegative and bounded by
`√2 · x⁻²`. -/
private lemma norm_le {x : ℝ} (hx : Real.sqrt 2 < x) :
    ‖((Real.sqrt (x^2-1))⁻¹ - x⁻¹) * Real.sqrt x‖ ≤ Real.sqrt 2 * x ^ (-2:ℝ) := by
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · rw [eq_div_of_sqrt_sub_one hx]
    set s := Real.sqrt (x^2-1) with hs_def
    have hxpos : 0 < x := by
      have h1 : (1:ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two; linarith
    have hx1 : 1 < x := by
      have h1 : (1:ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two; linarith
    have h2 : (2:ℝ) < x^2 := by
      have hsq : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2, hx, hsq]
    have hx21 : 0 < x^2 - 1 := by linarith
    have hs2 : s^2 = x^2 - 1 := Real.sq_sqrt (le_of_lt hx21)
    have hspos : 0 < s := by rw [Real.sqrt_pos]; exact hx21
    have hs_ge : x / Real.sqrt 2 ≤ s := by
      have hs2' : (x / Real.sqrt 2)^2 ≤ x^2 - 1 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        nlinarith [h2]
      calc x / Real.sqrt 2 = Real.sqrt ((x/Real.sqrt 2)^2) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ Real.sqrt (x^2 - 1) := Real.sqrt_le_sqrt hs2'
        _ = s := rfl
    have hden_ge : x^3 / Real.sqrt 2 ≤ x * s * (x + s) := by
      have h1 : x * (x / Real.sqrt 2) ≤ x * s := mul_le_mul_of_nonneg_left hs_ge hxpos.le
      have h2' : x ≤ x + s := by linarith [hspos.le]
      have h3 : 0 ≤ x * s := by positivity
      have h4 : x * (x / Real.sqrt 2) * x ≤ x * s * (x + s) :=
        mul_le_mul h1 h2' hxpos.le h3
      have h5 : x * (x / Real.sqrt 2) * x = x^3 / Real.sqrt 2 := by field_simp
      rwa [h5] at h4
    have hden_pos : 0 < x^3 / Real.sqrt 2 := by positivity
    have hstep1 : Real.sqrt x / (x*s*(x+s)) ≤ Real.sqrt x / (x^3 / Real.sqrt 2) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg x) hden_pos hden_ge
    have hsimp : Real.sqrt x / (x^3 / Real.sqrt 2) = Real.sqrt 2 * Real.sqrt x / x^3 := by
      field_simp
    rw [hsimp] at hstep1
    have hsqrt_le : Real.sqrt x ≤ x := by
      rw [Real.sqrt_le_self_iff]; right; linarith
    have hxx : Real.sqrt 2 * Real.sqrt x / x^3 ≤ Real.sqrt 2 * x / x^3 := by
      gcongr
    have hx2 : Real.sqrt 2 * x / x^3 = Real.sqrt 2 * x^(-2:ℝ) := by
      rw [Real.rpow_neg hxpos.le, Real.rpow_two]; field_simp
    linarith [hstep1, hxx, hx2.le]
  · rw [eq_div_of_sqrt_sub_one hx]
    have hxpos : 0 < x := by
      have h1 : (1:ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two; linarith
    have hx21 : 0 < x^2 - 1 := by
      have h2 : (2:ℝ) < x^2 := by
        have hsq : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
        nlinarith [Real.sqrt_nonneg 2, hx, hsq]
      linarith
    have hspos : 0 < Real.sqrt (x^2-1) := by rw [Real.sqrt_pos]; exact hx21
    positivity

theorem integrableOn_sqrt_sq_sub_one_Ioi_sqrt_two :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => ((Real.sqrt (x^2-1))⁻¹ - x⁻¹) * Real.sqrt x) (Set.Ioi (Real.sqrt 2)) := by
  have hg : MeasureTheory.IntegrableOn (fun x : ℝ => Real.sqrt 2 * x ^ (-2:ℝ))
      (Set.Ioi (Real.sqrt 2)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -2) (c := Real.sqrt 2)
      (by norm_num) (by positivity)).const_mul (Real.sqrt 2)
  have hmeas : Measurable
      (fun x : ℝ => ((Real.sqrt (x^2-1))⁻¹ - x⁻¹) * Real.sqrt x) := by measurability
  refine hg.mono' (hmeas.aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_le hx

end Commons.Analysis.Integral