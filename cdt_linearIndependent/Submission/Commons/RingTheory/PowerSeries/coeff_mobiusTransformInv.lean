import Mathlib
import Submission.Commons.RingTheory.PowerSeries.coeff_inv_one_sub_C_mul_pow
import Submission.Commons.RingTheory.PowerSeries.coeff_mobiusTransform

namespace Commons.RingTheory.PowerSeries

open _root_.PowerSeries

/-- Coefficient of `(1-X)⁻¹ * (X * (1-X)⁻¹)^m`. -/
lemma coeff_inv_one_sub_X_mul_pow (m n : ℕ) :
    PowerSeries.coeff n (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹
        * (PowerSeries.X * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) ^ m)
      = ((Nat.choose n m : ℕ) : ℚ) := by
  have hpow : ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹
        * (PowerSeries.X * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) ^ m
      = PowerSeries.X ^ m * (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) ^ (m + 1) := by
    rw [mul_pow]
    ring
  rw [hpow, PowerSeries.coeff_X_pow_mul']
  by_cases hm : m ≤ n
  · rw [if_pos hm]
    have h := coeff_inv_one_sub_C_mul_pow ℚ (1 : ℚ) (n - m) m
    have hC1 : (1 : PowerSeries ℚ) - PowerSeries.C (1 : ℚ) * PowerSeries.X
        = 1 - PowerSeries.X := by
      rw [map_one, one_mul]
    rw [hC1] at h
    rw [h, Nat.sub_add_cancel hm]
    simp
  · rw [if_neg hm, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hm)]
    simp

theorem coeff_mobiusTransformInv (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹
        * f.subst (PowerSeries.X * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹))
      = ∑ m ∈ Finset.range (n + 1), PowerSeries.coeff m f * ((Nat.choose n m : ℕ) : ℚ) := by
  set T : PowerSeries ℚ := PowerSeries.X * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ with hTdef
  have hT : T.constantCoeff = 0 := by rw [hTdef]; simp
  have hU : ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ = 1 + T := by
    have hcc : PowerSeries.constantCoeff ((1 : PowerSeries ℚ) - PowerSeries.X) ≠ 0 := by simp
    have h : (1 + T) * ((1 : PowerSeries ℚ) - PowerSeries.X) = 1 := by
      rw [hTdef, add_mul, one_mul, mul_assoc, PowerSeries.inv_mul_cancel _ hcc, mul_one]
      ring
    exact ((PowerSeries.eq_inv_iff_mul_eq_one hcc).mpr h).symm
  have hTsubst : HasSubst T := PowerSeries.HasSubst.of_constantCoeff_zero' hT
  have hg : ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ * f.subst T
      = f.subst T + (PowerSeries.X * f).subst T := by
    rw [hU, add_mul, one_mul]
    rw [PowerSeries.subst_mul hTsubst PowerSeries.X f, PowerSeries.subst_X hTsubst]
  have hcoeffX : ∀ d : ℕ, PowerSeries.coeff d (PowerSeries.X * f)
      = if d = 0 then 0 else PowerSeries.coeff (d - 1) f := by
    intro d
    rw [show (PowerSeries.X : PowerSeries ℚ) * f = PowerSeries.X ^ 1 * f by rw [pow_one]]
    rw [PowerSeries.coeff_X_pow_mul']
    by_cases hd : d = 0
    · subst hd; simp
    · rw [if_pos (Nat.one_le_iff_ne_zero.mpr hd), if_neg hd]
  have hC0 : PowerSeries.coeff n (T ^ (n + 1)) = 0 := by
    rw [PowerSeries.coeff_of_lt_order n ?_]
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n)
      (le_order_pow_of_constantCoeff_eq_zero (n + 1) hT)
  have hKey : ∀ m : ℕ, PowerSeries.coeff n (T ^ m) + PowerSeries.coeff n (T ^ (m + 1))
      = ((Nat.choose n m : ℕ) : ℚ) := by
    intro m
    rw [← map_add]
    have hsum : T ^ m + T ^ (m + 1)
        = ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ * T ^ m := by
      rw [hU, pow_succ]; ring
    rw [hsum, hTdef, coeff_inv_one_sub_X_mul_pow m n]
  have hB1 : (∑ d ∈ Finset.range (n + 1),
        PowerSeries.coeff d (PowerSeries.X * f) * PowerSeries.coeff n (T ^ d))
      = ∑ k ∈ Finset.range n, PowerSeries.coeff k f * PowerSeries.coeff n (T ^ (k + 1)) := by
    rw [Finset.sum_congr rfl (fun d _ => by rw [hcoeffX d])]
    rw [Finset.sum_range_succ']
    rw [show (if (0 : ℕ) = 0 then 0 else PowerSeries.coeff (0 - 1) f)
          * PowerSeries.coeff n (T ^ 0) = 0 by simp, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
  have hB2 : (∑ k ∈ Finset.range n,
        PowerSeries.coeff k f * PowerSeries.coeff n (T ^ (k + 1)))
      = ∑ m ∈ Finset.range (n + 1),
          PowerSeries.coeff m f * PowerSeries.coeff n (T ^ (m + 1)) := by
    rw [Finset.sum_range_succ, hC0, mul_zero, add_zero]
  rw [hg, map_add]
  rw [coeff_subst_eq_sum_range f T hT n, coeff_subst_eq_sum_range (PowerSeries.X * f) T hT n]
  rw [hB1, hB2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_add, hKey m]

end Commons.RingTheory.PowerSeries
