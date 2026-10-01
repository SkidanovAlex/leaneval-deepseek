import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Commons.NumberTheory.Linnik

open Complex
open scoped BigOperators

/-- For a complex number `w` with nonnegative real part, `‖1 - exp (-w)‖ ≤ ‖w‖`.
This is the standard estimate `|1 - e^{-w}| ≤ |w|` (for `Re w ≥ 0`), obtained by
writing `1 - exp (-w) = ∫ x in 0..1, w * exp (-x • w)` (fundamental theorem of
calculus) and bounding the integral by the norm of the integrand, which is at
most `‖w‖` because `‖exp (-x • w)‖ = exp (-x * Re w) ≤ 1` for `0 < x ≤ 1`. -/
theorem norm_one_sub_exp_neg_le (w : ℂ) (hw : 0 ≤ w.re) :
    ‖1 - Complex.exp (-w)‖ ≤ ‖w‖ := by
  by_cases hw0 : w = 0
  · subst w
    simp
  · have hc : -w ≠ 0 := neg_ne_zero.mpr hw0
    have hbasic : (∫ x : ℝ in 0..1, Complex.exp ((-w) * (x : ℂ))) =
        (Complex.exp (-w) - 1) / (-w) := by
      have h := integral_exp_mul_complex (a := (0 : ℝ)) (b := 1) (c := -w) hc
      simpa using h
    have h_int_id : (∫ x : ℝ in 0..1, w * Complex.exp (-((x : ℂ) * w))) =
        1 - Complex.exp (-w) := by
      calc
        (∫ x : ℝ in 0..1, w * Complex.exp (-((x : ℂ) * w)))
            = (∫ x : ℝ in 0..1, w * Complex.exp ((-w) * (x : ℂ))) := by
              apply intervalIntegral.integral_congr
              intro x hx
              ring_nf
        _ = w * (∫ x : ℝ in 0..1, Complex.exp ((-w) * (x : ℂ))) := by
              rw [intervalIntegral.integral_const_mul]
        _ = w * ((Complex.exp (-w) - 1) / (-w)) := by rw [hbasic]
        _ = 1 - Complex.exp (-w) := by
              field_simp [hc]
              ring
    have hnorm : ∀ x ∈ Set.uIoc (0 : ℝ) 1,
        ‖w * Complex.exp (-((x : ℂ) * w))‖ ≤ ‖w‖ := by
      intro x hx
      have hxpos : 0 < x := by
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        exact hx.1
      have hprod : 0 ≤ x * w.re := mul_nonneg (le_of_lt hxpos) hw
      have h_exp_le : Real.exp (-(x * w.re)) ≤ Real.exp (0 : ℝ) := by
        exact Real.exp_le_exp.mpr (by linarith)
      calc
        ‖w * Complex.exp (-((x : ℂ) * w))‖ = ‖w‖ * ‖Complex.exp (-((x : ℂ) * w))‖ := by
          rw [norm_mul]
        _ = ‖w‖ * Real.exp (-((x : ℂ) * w)).re := by rw [Complex.norm_exp]
        _ = ‖w‖ * Real.exp (-(x * w.re)) := by
          rw [Complex.neg_re, Complex.re_ofReal_mul]
        _ ≤ ‖w‖ * Real.exp (0 : ℝ) := mul_le_mul_of_nonneg_left h_exp_le (norm_nonneg w)
        _ = ‖w‖ := by simp
    calc
      ‖1 - Complex.exp (-w)‖ = ‖∫ x : ℝ in 0..1, w * Complex.exp (-((x : ℂ) * w))‖ := by
        rw [← h_int_id]
      _ ≤ ‖w‖ := by
        exact (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
          (C := ‖w‖) hnorm).trans (by simp)

end Commons.NumberTheory.Linnik