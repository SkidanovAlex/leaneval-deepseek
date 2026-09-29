import Mathlib
import Submission.Commons.Analysis.Integral.integral_tsum_interval
import Submission.Commons.Analysis.Integral.squareInverseKernelDoubleIntegral
import Submission.Commons.Analysis.Integral.doubleIntegral_inv_one_sub_mul
import Submission.Commons.Analysis.InfiniteSum.sum_zetaJ_series
import Submission.Commons.Analysis.InfiniteSum.hasSum_succ_mul_geometric

noncomputable section

namespace Commons.Analysis.Integral

open MeasureTheory
open scoped Interval BigOperators

/-- `∫₀¹ (1 - t²) tⁿ dt = 2/((n+1)(n+3))`. -/
lemma integral_one_sub_sq_mul_pow (n : ℕ) :
    (∫ t in (0 : ℝ)..1, (1 - t ^ 2) * t ^ n) = 2 / (((n : ℝ) + 1) * ((n : ℝ) + 3)) := by
  have hcongr : (∫ t in (0 : ℝ)..1, (1 - t ^ 2) * t ^ n)
      = ∫ t in (0 : ℝ)..1, (t ^ n - t ^ (n + 2)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only []
    have hkey : (1 - t ^ 2) * t ^ n = t ^ n - t ^ (n + 2) := by
      rw [pow_add]
      ring
    exact hkey
  rw [hcongr, intervalIntegral.integral_sub]
  · rw [intervalIntegral_pow_zero_one n, intervalIntegral_pow_zero_one (n + 2)]
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h3 : ((n : ℝ) + 3) ≠ 0 := by positivity
    have hc : (((n + 2 : ℕ) : ℝ) + 1) = (n : ℝ) + 3 := by push_cast; ring
    rw [hc]
    field_simp; ring
  · exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
  · exact Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1

/-- The `n`-th summand of the geometric expansion of `(1-t²)/(1-st)²`. -/
lemma innerTerm_eq (s : ℝ) (n : ℕ) (t : ℝ) :
    (1 - t ^ 2) * (((n : ℝ) + 1) * (s * t) ^ n)
      = ((n : ℝ) + 1) * s ^ n * ((1 - t ^ 2) * t ^ n) := by
  rw [mul_pow]
  ring

/-- `∫₀¹ (1-t²)·((n+1)(st)ⁿ) dt = 2 sⁿ/(n+3)`. -/
lemma innerTerm_integral (s : ℝ) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, (1 - t ^ 2) * (((n : ℝ) + 1) * (s * t) ^ n))
      = 2 * s ^ n / ((n : ℝ) + 3) := by
  rw [intervalIntegral.integral_congr (fun t _ => innerTerm_eq s n t)]
  rw [intervalIntegral.integral_const_mul, integral_one_sub_sq_mul_pow n]
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h3 : ((n : ℝ) + 3) ≠ 0 := by positivity
  field_simp

/-- Norm version of `innerTerm_integral` for `s ≥ 0`. -/
lemma innerTerm_norm_integral (s : ℝ) (hs0 : 0 ≤ s) (n : ℕ) :
    (∫ t in (0 : ℝ)..1, ‖(1 - t ^ 2) * (((n : ℝ) + 1) * (s * t) ^ n)‖)
      = 2 * s ^ n / ((n : ℝ) + 3) := by
  have h : (∫ t in (0 : ℝ)..1, ‖(1 - t ^ 2) * (((n : ℝ) + 1) * (s * t) ^ n)‖)
      = ∫ t in (0 : ℝ)..1, (1 - t ^ 2) * (((n : ℝ) + 1) * (s * t) ^ n) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simp only []
    have hnon : 0 ≤ (1 - t ^ 2) * (((n : ℝ) + 1) * (s * t) ^ n) := by
      apply mul_nonneg
      · nlinarith [ht.1, ht.2]
      · apply mul_nonneg (by positivity)
        exact pow_nonneg (mul_nonneg hs0 ht.1) n
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
  rw [h, innerTerm_integral s n]

/-- Summability of the norm integrals of the inner summands, for `0 ≤ s < 1`. -/
lemma summable_innerTerm_norm (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun n : ℕ =>
      ∫ t in (0 : ℝ)..1, ‖(1 - t ^ 2) * (((n : ℝ) + 1) * (s * t) ^ n)‖) := by
  have hfun : (fun n : ℕ =>
        ∫ t in (0 : ℝ)..1, ‖(1 - t ^ 2) * (((n : ℝ) + 1) * (s * t) ^ n)‖)
      = fun n : ℕ => 2 * s ^ n / ((n : ℝ) + 3) :=
    funext (fun n => innerTerm_norm_integral s hs0 n)
  rw [hfun]
  apply Summable.of_nonneg_of_le (f := fun n : ℕ => 2 * s ^ n)
  · intro n
    exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs0 n)) (by positivity)
  · intro n
    exact div_le_self (mul_nonneg (by norm_num) (pow_nonneg hs0 n)) (by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
  · exact (summable_geometric_of_lt_one hs0 hs1).mul_left 2

/-- **Inner integral.** For `0 ≤ s < 1`, `∫₀¹ (1-t²)/(1-st)² dt = ∑ₙ 2 sⁿ/(n+3)`. -/
lemma innerIntegral_zetaJ_eq_tsum {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ t in (0 : ℝ)..1, (1 - t ^ 2) / (1 - s * t) ^ 2)
      = ∑' n : ℕ, 2 * s ^ n / ((n : ℝ) + 3) := by
  have hgeom : (∫ t in (0 : ℝ)..1, (1 - t ^ 2) / (1 - s * t) ^ 2)
      = ∫ t in (0 : ℝ)..1,
          ∑' n : ℕ, (1 - t ^ 2) * (((n : ℝ) + 1) * (s * t) ^ n) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hst : ‖s * t‖ < 1 := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs0, abs_of_nonneg ht0]
      calc s * t ≤ s * 1 := mul_le_mul_of_nonneg_left ht1 hs0
        _ = s := mul_one s
        _ < 1 := hs1
    have hseries : (∑' n : ℕ, ((n : ℝ) + 1) * (s * t) ^ n) = 1 / (1 - s * t) ^ 2 :=
      (Commons.Analysis.InfiniteSum.hasSum_succ_mul_geometric hst).tsum_eq
    simp only []
    rw [div_eq_mul_one_div, ← hseries, ← tsum_mul_left]
  have hf : ∀ n : ℕ,
      IntervalIntegrable (fun t : ℝ => (1 - t ^ 2) * (((n : ℝ) + 1) * (s * t) ^ n)) volume
        (0 : ℝ) 1 :=
    fun n => Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1
  have hsum := summable_innerTerm_norm s hs0 hs1
  rw [hgeom, (integral_tsum_interval
    (f := fun n t => (1 - t ^ 2) * (((n : ℝ) + 1) * (s * t) ^ n)) hf hsum).symm]
  apply tsum_congr
  intro n
  exact innerTerm_integral s n

/-- An algebraic rearrangement of the outer summand. -/
lemma outerTerm_eq (n : ℕ) (s : ℝ) :
    (1 - s ^ 2) * (2 * s ^ n / ((n : ℝ) + 3))
      = (2 / ((n : ℝ) + 3)) * ((1 - s ^ 2) * s ^ n) := by
  ring

/-- `∫₀¹ (1-s²)·(2 sⁿ/(n+3)) ds = 4/((n+1)(n+3)²)`. -/
lemma outerTerm_integral (n : ℕ) :
    (∫ s in (0 : ℝ)..1, (1 - s ^ 2) * (2 * s ^ n / ((n : ℝ) + 3)))
      = 4 / (((n : ℝ) + 1) * ((n : ℝ) + 3) ^ 2) := by
  rw [intervalIntegral.integral_congr (fun s _ => outerTerm_eq n s)]
  rw [intervalIntegral.integral_const_mul, integral_one_sub_sq_mul_pow n]
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h3 : ((n : ℝ) + 3) ≠ 0 := by positivity
  field_simp; ring

/-- Norm version of `outerTerm_integral`. -/
lemma outerTerm_norm_integral (n : ℕ) :
    (∫ s in (0 : ℝ)..1, ‖(1 - s ^ 2) * (2 * s ^ n / ((n : ℝ) + 3))‖)
      = 4 / (((n : ℝ) + 1) * ((n : ℝ) + 3) ^ 2) := by
  have h : (∫ s in (0 : ℝ)..1, ‖(1 - s ^ 2) * (2 * s ^ n / ((n : ℝ) + 3))‖)
      = ∫ s in (0 : ℝ)..1, (1 - s ^ 2) * (2 * s ^ n / ((n : ℝ) + 3)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    simp only []
    have hnon : 0 ≤ (1 - s ^ 2) * (2 * s ^ n / ((n : ℝ) + 3)) := by
      apply mul_nonneg
      · nlinarith [hs.1, hs.2]
      · exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs.1 n)) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
  rw [h, outerTerm_integral n]

/-- Summability of the norm integrals of the outer summands. -/
lemma summable_outerTerm_norm :
    Summable (fun n : ℕ =>
      ∫ s in (0 : ℝ)..1, ‖(1 - s ^ 2) * (2 * s ^ n / ((n : ℝ) + 3))‖) := by
  have hfun : (fun n : ℕ =>
        ∫ s in (0 : ℝ)..1, ‖(1 - s ^ 2) * (2 * s ^ n / ((n : ℝ) + 3))‖)
      = fun n : ℕ => 4 / (((n : ℝ) + 1) * ((n : ℝ) + 3) ^ 2) :=
    funext (fun n => outerTerm_norm_integral n)
  rw [hfun]
  apply Summable.of_nonneg_of_le (f := fun n : ℕ => 4 * (1 / ((n : ℝ) + 1) ^ 2))
  · intro n
    exact div_nonneg (by norm_num) (by positivity)
  · intro n
    rw [mul_one_div]
    have hle : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) * ((n : ℝ) + 3) ^ 2 := by
      have h3 : (1 : ℝ) ≤ (n : ℝ) + 3 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hsq : (n : ℝ) + 1 ≤ ((n : ℝ) + 3) ^ 2 := by
        have h4 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [sq_nonneg ((n : ℝ) + 2), h4, h3]
      calc ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) * ((n : ℝ) + 1) := by ring
        _ ≤ ((n : ℝ) + 1) * ((n : ℝ) + 3) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hle
  · exact summable_one_div_succ_sq.mul_left 4

/-- **Outer interchange.** `∫₀¹ (1-s²) (∑ₙ 2 sⁿ/(n+3)) ds = ∑ₙ ∫₀¹ (1-s²)(2 sⁿ/(n+3)) ds`. -/
lemma outerIntegral_zetaJ_eq_tsum :
    (∫ s in (0 : ℝ)..1, (1 - s ^ 2) * (∑' n : ℕ, 2 * s ^ n / ((n : ℝ) + 3)))
      = ∑' n : ℕ,
          ∫ s in (0 : ℝ)..1, (1 - s ^ 2) * (2 * s ^ n / ((n : ℝ) + 3)) := by
  have hcongr : (∫ s in (0 : ℝ)..1, (1 - s ^ 2) * (∑' n : ℕ, 2 * s ^ n / ((n : ℝ) + 3)))
      = ∫ s in (0 : ℝ)..1,
          ∑' n : ℕ, (1 - s ^ 2) * (2 * s ^ n / ((n : ℝ) + 3)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    simp only []
    exact (tsum_mul_left (a := 1 - s ^ 2) (f := fun n : ℕ => 2 * s ^ n / ((n : ℝ) + 3))).symm
  rw [hcongr]
  exact (integral_tsum_interval
    (f := fun n s => (1 - s ^ 2) * (2 * s ^ n / ((n : ℝ) + 3)))
    (fun n => Continuous.intervalIntegrable (by fun_prop) (0 : ℝ) 1)
    summable_outerTerm_norm).symm

theorem doubleIntegral_zetaJ_one :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        (1 - s ^ 2) * (1 - t ^ 2) / (1 - s * t) ^ 2)
      = 4 - 2 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
  have hstep1 : (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
        (1 - s ^ 2) * (1 - t ^ 2) / (1 - s * t) ^ 2)
      = ∫ s in (0 : ℝ)..1,
          (1 - s ^ 2) * (∫ t in (0 : ℝ)..1, (1 - t ^ 2) / (1 - s * t) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro s hs
    simp only []
    have hsplit : (∫ t in (0 : ℝ)..1, (1 - s ^ 2) * (1 - t ^ 2) / (1 - s * t) ^ 2)
        = ∫ t in (0 : ℝ)..1, (1 - s ^ 2) * ((1 - t ^ 2) / (1 - s * t) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only []
      rw [mul_div_assoc]
    rw [hsplit, intervalIntegral.integral_const_mul]
  have hstep2 : (∫ s in (0 : ℝ)..1,
        (1 - s ^ 2) * (∫ t in (0 : ℝ)..1, (1 - t ^ 2) / (1 - s * t) ^ 2))
      = ∫ s in (0 : ℝ)..1,
          (1 - s ^ 2) * (∑' n : ℕ, 2 * s ^ n / ((n : ℝ) + 3)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) (1 : ℝ)] with s hsne
    intro hsI
    have hsI' : s ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hsI
    have hs0 : 0 ≤ s := le_of_lt hsI'.1
    have hslt : s < 1 := lt_of_le_of_ne hsI'.2 hsne
    rw [innerIntegral_zetaJ_eq_tsum hs0 hslt]
  have hstep3 : (∫ s in (0 : ℝ)..1,
        (1 - s ^ 2) * (∑' n : ℕ, 2 * s ^ n / ((n : ℝ) + 3)))
      = ∑' n : ℕ,
          ∫ s in (0 : ℝ)..1, (1 - s ^ 2) * (2 * s ^ n / ((n : ℝ) + 3)) :=
    outerIntegral_zetaJ_eq_tsum
  have hstep4 : (∑' n : ℕ,
        ∫ s in (0 : ℝ)..1, (1 - s ^ 2) * (2 * s ^ n / ((n : ℝ) + 3)))
      = ∑' n : ℕ, 4 / (((n : ℝ) + 1) * ((n : ℝ) + 3) ^ 2) := by
    apply tsum_congr
    intro n
    exact outerTerm_integral n
  rw [hstep1, hstep2, hstep3, hstep4]
  exact Commons.Analysis.InfiniteSum.sum_zetaJ_series

end Commons.Analysis.Integral
