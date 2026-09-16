import Mathlib
import Submission.Commons.MeasureTheory.Integral.beta_integral

open MeasureTheory intervalIntegral

namespace Commons.MeasureTheory.Integral

/-- The beta integral over the unit interval `[0,1]`, in the interval-integral form. -/
private lemma beta_interval01 (a b : ℕ) :
    ∫ x in (0 : ℝ)..1, (1 - x) ^ a * x ^ b =
      (((a.factorial * b.factorial : ℕ)) : ℝ) / (((a + b + 1).factorial : ℕ) : ℝ) := by
  have h := beta_integral a b
  rw [← integral_Ioc_eq_integral_Ioo,
    ← integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at h
  exact h

/-- The beta integral with a general upper limit `L ≥ 0`:
`∫₀^L (L - x)^a x^b dx = L^(a+b+1) · a! b! / (a+b+1)!`. -/
theorem beta_integral_scaled {L : ℝ} (hL : 0 ≤ L) (a b : ℕ) :
    ∫ x in (0:ℝ)..L, (L - x) ^ a * x ^ b
      = L ^ (a + b + 1) * (((a.factorial * b.factorial : ℕ)) : ℝ) /
          (((a + b + 1).factorial : ℕ) : ℝ) := by
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · subst hL0
    simp [zero_pow (Nat.succ_ne_zero (a + b))]
  · have hLne : L ≠ 0 := ne_of_gt hLpos
    have hgm : (fun x : ℝ => (L - x) ^ a * x ^ b)
        = fun x : ℝ => L ^ (a + b) * ((1 - x / L) ^ a * (x / L) ^ b) := by
      funext x
      have h1 : L ^ a * (1 - x / L) ^ a = (L - x) ^ a := by
        rw [← mul_pow]
        congr 1
        field_simp
      have h2 : L ^ b * (x / L) ^ b = x ^ b := by
        rw [← mul_pow]
        congr 1
        field_simp
      rw [pow_add, ← h1, ← h2]
      ring
    calc
      ∫ x in (0:ℝ)..L, (L - x) ^ a * x ^ b
          = ∫ x in (0:ℝ)..L, L ^ (a + b) * ((1 - x / L) ^ a * (x / L) ^ b) := by
            rw [hgm]
      _ = L ^ (a + b) * ∫ x in (0:ℝ)..L, (1 - x / L) ^ a * (x / L) ^ b := by
            rw [intervalIntegral.integral_const_mul]
      _ = L ^ (a + b) * (L * ∫ y in (0:ℝ)..1, (1 - y) ^ a * y ^ b) := by
            rw [intervalIntegral.integral_comp_div (fun y : ℝ => (1 - y) ^ a * y ^ b) hLne]
            simp [smul_eq_mul, div_self hLne]
      _ = L ^ (a + b + 1) * (((a.factorial * b.factorial : ℕ)) : ℝ) /
            (((a + b + 1).factorial : ℕ) : ℝ) := by
            rw [beta_interval01, pow_succ]
            ring

end Commons.MeasureTheory.Integral
