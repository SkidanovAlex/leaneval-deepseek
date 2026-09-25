import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Cauchy–Schwarz for the Lebesgue integral of `ℝ≥0∞`-valued functions

For `AEMeasurable` functions `f h : α → ℝ≥0∞` one has

  `(∫⁻ a, f a * h a) ^ 2 ≤ (∫⁻ a, f a) * (∫⁻ a, f a * h a ^ 2)`.

This is Cauchy–Schwarz applied to the density `f`; it is obtained from Hölder's inequality
(`ENNReal.lintegral_mul_norm_pow_le`) with exponents `p = q = 1/2`, using
`f a ^ (1/2) * (f a * h a ^ 2) ^ (1/2) = f a * h a`.
-/

namespace Commons.Analysis.MeasureTheory

open _root_.MeasureTheory
open scoped ENNReal

private lemma rpow_half_mul_self (x : ℝ≥0∞) :
    x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
  have h := ENNReal.rpow_add_of_nonneg (x := x) ((1 : ℝ) / 2) ((1 : ℝ) / 2)
    (by norm_num) (by norm_num)
  rw [show ((1 : ℝ) / 2 + 1 / 2) = 1 by norm_num, ENNReal.rpow_one] at h
  exact h.symm

private lemma rpow_half_pow_two (x : ℝ≥0∞) :
    (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem sq_lintegral_mul_le_mul_lintegral_mul_sq {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f h : α → ENNReal}
    (hf : AEMeasurable f μ) (hh : AEMeasurable h μ) :
    (MeasureTheory.lintegral μ (fun a => f a * h a)) ^ 2 ≤
      MeasureTheory.lintegral μ (fun a => f a) *
        MeasureTheory.lintegral μ (fun a => f a * h a ^ 2) := by
  have hg : AEMeasurable (fun y => f y * h y ^ 2) μ := hf.mul (hh.pow_const 2)
  -- Hölder with `p = q = 1/2` applied to `f` and `f * h ^ 2`
  have hholder := ENNReal.lintegral_mul_norm_pow_le (μ := μ) hf hg
    (p := (1 : ℝ) / 2) (q := (1 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num)
  -- the pointwise identity making the integrand on the left equal to `f * h`
  have hpt : ∀ y, f y ^ ((1 : ℝ) / 2) * (f y * h y ^ 2) ^ ((1 : ℝ) / 2) = f y * h y := by
    intro y
    have hb : (f y * h y ^ 2) ^ ((1 : ℝ) / 2) = f y ^ ((1 : ℝ) / 2) * h y := by
      rw [ENNReal.mul_rpow_of_nonneg (f y) (h y ^ 2) (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
      congr 1
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [hb, ← mul_assoc, rpow_half_mul_self]
  rw [lintegral_congr hpt] at hholder
  calc (MeasureTheory.lintegral μ (fun a => f a * h a)) ^ 2
      ≤ (((MeasureTheory.lintegral μ (fun a => f a)) ^ ((1 : ℝ) / 2)) *
          ((MeasureTheory.lintegral μ (fun a => f a * h a ^ 2)) ^ ((1 : ℝ) / 2))) ^ 2 :=
        ENNReal.pow_le_pow_left (n := 2) hholder
    _ = (MeasureTheory.lintegral μ (fun a => f a)) *
          (MeasureTheory.lintegral μ (fun a => f a * h a ^ 2)) := by
        rw [mul_pow, rpow_half_pow_two, rpow_half_pow_two]

end Commons.Analysis.MeasureTheory
