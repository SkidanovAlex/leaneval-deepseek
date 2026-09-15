import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Data.Nat.Totient
import Submission.Commons.NumberTheory.Sieve.LambdaR_prime

namespace Commons.NumberTheory.Sieve

theorem nu_majorant_lower {R W n k : ℕ} (hR : 0 < R) (hk : 0 < k)
    (hlogR : 0 < Real.log (R : ℝ))
    (hLog : 0 ≤ Real.log (((W * n + 1 : ℕ) : ℝ)))
    (hRn : R < W * n + 1) (hprime : Nat.Prime (W * n + 1))
    (hbound : Real.log (((W * n + 1 : ℕ) : ℝ)) ≤ (k : ℝ) * (2 : ℝ) ^ (k + 5) * Real.log (R : ℝ)) :
    ((Nat.totient W : ℝ) / (W : ℝ)) * (k : ℝ)⁻¹ * (2 : ℝ) ^ (-(k : ℤ) - 5) *
        Real.log (((W * n + 1 : ℕ) : ℝ))
      ≤ ((Nat.totient W : ℝ) / (W : ℝ)) *
        (LambdaR R (W * n + 1) ^ 2 / Real.log (R : ℝ)) := by
  have hL : LambdaR R (W * n + 1) = Real.log (R : ℝ) := LambdaR_prime hprime hRn
  rw [hL]
  have hlogRne : Real.log (R : ℝ) ≠ 0 := ne_of_gt hlogR
  have hsq : Real.log (R : ℝ) ^ 2 / Real.log (R : ℝ) = Real.log (R : ℝ) := by
    rw [pow_two, mul_div_cancel_left₀ _ hlogRne]
  rw [hsq]
  have hzpow : (2 : ℝ) ^ (-(k : ℤ) - 5) = ((2 : ℝ) ^ (k + 5))⁻¹ := by
    have h : (-(k : ℤ) - 5) = -((k + 5 : ℕ) : ℤ) := by push_cast; ring
    rw [h, zpow_neg, zpow_natCast]
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hstep : (k : ℝ)⁻¹ * ((2 : ℝ) ^ (k + 5))⁻¹ * Real.log (((W * n + 1 : ℕ) : ℝ))
      ≤ Real.log (R : ℝ) := by
    have hD : (0 : ℝ) < (k : ℝ) * (2 : ℝ) ^ (k + 5) :=
      mul_pos hkpos (by positivity)
    rw [← mul_inv, ← div_eq_inv_mul, div_le_iff₀ hD]
    nlinarith [hbound]
  calc
    (Nat.totient W : ℝ) / (W : ℝ) * (k : ℝ)⁻¹ * (2 : ℝ) ^ (-(k : ℤ) - 5) *
        Real.log (((W * n + 1 : ℕ) : ℝ))
        = (Nat.totient W : ℝ) / (W : ℝ) *
            ((k : ℝ)⁻¹ * ((2 : ℝ) ^ (k + 5))⁻¹ * Real.log (((W * n + 1 : ℕ) : ℝ))) := by
          rw [hzpow]; ring
    _ ≤ (Nat.totient W : ℝ) / (W : ℝ) * Real.log (R : ℝ) :=
        mul_le_mul_of_nonneg_left hstep (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end Commons.NumberTheory.Sieve