import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PowerSeries.Substitution
import Submission.Commons.RingTheory.PowerSeries.coeff_inv_one_sub_C_mul_pow

namespace Commons.RingTheory.PowerSeries

open _root_.PowerSeries

/-- Coefficient formula for substitution into a power series `t` with vanishing constant
coefficient: the `n`-th coefficient of `h.subst t` only involves the coefficients of `h`
up to `n`. -/
lemma coeff_subst_eq_sum_range (h t : PowerSeries ℚ) (ht : t.constantCoeff = 0) (n : ℕ) :
    PowerSeries.coeff n (h.subst t) =
      ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d h * PowerSeries.coeff n (t ^ d) := by
  have ht' : HasSubst t := PowerSeries.HasSubst.of_constantCoeff_zero' ht
  rw [PowerSeries.coeff_subst' ht' h n]
  have hsupp : Function.support
        (fun d : ℕ => PowerSeries.coeff d h • PowerSeries.coeff n (t ^ d))
      ⊆ ↑(Finset.range (n + 1)) := by
    intro d hd
    simp only [Function.mem_support] at hd
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hcon
    refine hd ?_
    have hnd : n < d := Nat.lt_of_succ_le (Nat.not_lt.mp hcon)
    rw [smul_eq_mul, PowerSeries.coeff_of_lt_order n ?_, mul_zero]
    exact lt_of_lt_of_le (by exact_mod_cast hnd)
      (le_order_pow_of_constantCoeff_eq_zero d ht)
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun d _ => by rw [smul_eq_mul]

/-- Coefficient of `(1+X)⁻¹ * (X * (1+X)⁻¹)^m`. -/
lemma coeff_inv_add_one_X_mul_pow (m n : ℕ) :
    PowerSeries.coeff n (((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹
        * (PowerSeries.X * ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹) ^ m)
      = (-1) ^ (n - m) * ((Nat.choose n m : ℕ) : ℚ) := by
  have hmul : ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹
        * (PowerSeries.X * ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹) ^ m
      = PowerSeries.X ^ m * (((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹) ^ (m + 1) := by
    rw [mul_pow]
    ring
  rw [hmul, PowerSeries.coeff_X_pow_mul']
  have hX1 : (1 : PowerSeries ℚ) - PowerSeries.C (-1) * PowerSeries.X
      = (PowerSeries.X : PowerSeries ℚ) + 1 := by
    rw [map_neg, map_one, neg_mul, one_mul]
    ring
  by_cases hm : m ≤ n
  · rw [if_pos hm, ← hX1, coeff_inv_one_sub_C_mul_pow ℚ (-1) (n - m) m,
      Nat.sub_add_cancel hm]
    ring
  · rw [if_neg hm, Nat.sub_eq_zero_of_le (le_of_lt (Nat.lt_of_not_le hm)),
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le hm)]
    simp

/-- Summation by parts for a finite sum. -/
lemma sum_range_sub_mul_shift (A C : ℕ → ℚ) (n : ℕ) (hC : C (n + 1) = 0) :
    (∑ d ∈ Finset.range (n + 1), A d * C d)
        - (∑ d ∈ Finset.range n, A d * C (d + 1))
      = ∑ d ∈ Finset.range (n + 1), A d * (C d - C (d + 1)) := by
  have h1 : (∑ d ∈ Finset.range n, A d * C (d + 1))
      = ∑ d ∈ Finset.range (n + 1), A d * C (d + 1) := by
    rw [Finset.sum_range_succ, hC, mul_zero, add_zero]
  rw [h1, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => by ring

theorem coeff_mobiusTransform (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹
        * f.subst (PowerSeries.X * ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹))
      = ∑ m ∈ Finset.range (n + 1),
          PowerSeries.coeff m f * (-1) ^ (n - m) * ((Nat.choose n m : ℕ) : ℚ) := by
  set T : PowerSeries ℚ := PowerSeries.X * ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹ with hTdef
  have hT : T.constantCoeff = 0 := by rw [hTdef]; simp
  have hU : ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹ = 1 - T := by
    have hcc : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries ℚ) + 1) ≠ 0 := by simp
    have h : (1 - T) * ((PowerSeries.X : PowerSeries ℚ) + 1) = 1 := by
      rw [hTdef]
      rw [sub_mul, one_mul, mul_assoc, PowerSeries.inv_mul_cancel _ hcc, mul_one]
      ring
    exact ((PowerSeries.eq_inv_iff_mul_eq_one hcc).mpr h).symm
  have hTsubst : HasSubst T := PowerSeries.HasSubst.of_constantCoeff_zero' hT
  have hg : ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹ * f.subst T
      = f.subst T - (PowerSeries.X * f).subst T := by
    rw [hU, sub_mul, one_mul]
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
  rw [hg, map_sub]
  rw [coeff_subst_eq_sum_range f T hT n, coeff_subst_eq_sum_range (PowerSeries.X * f) T hT n]
  have h2 : (∑ d ∈ Finset.range (n + 1),
        PowerSeries.coeff d (PowerSeries.X * f) * PowerSeries.coeff n (T ^ d))
      = ∑ d ∈ Finset.range n, PowerSeries.coeff d f * PowerSeries.coeff n (T ^ (d + 1)) := by
    rw [Finset.sum_congr rfl (fun d _ => by rw [hcoeffX d])]
    rw [Finset.sum_range_succ']
    rw [show (if (0 : ℕ) = 0 then 0 else PowerSeries.coeff (0 - 1) f)
          * PowerSeries.coeff n (T ^ 0) = 0 by simp, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
  rw [h2, sum_range_sub_mul_shift (fun d => PowerSeries.coeff d f)
      (fun d => PowerSeries.coeff n (T ^ d)) n hC0]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hkey : PowerSeries.coeff n (T ^ d) - PowerSeries.coeff n (T ^ (d + 1))
      = (-1) ^ (n - d) * ((Nat.choose n d : ℕ) : ℚ) := by
    rw [← map_sub]
    rw [show T ^ d - T ^ (d + 1) = (1 - T) * T ^ d by ring]
    rw [← hU, hTdef]
    exact coeff_inv_add_one_X_mul_pow d n
  rw [hkey]
  ring

end Commons.RingTheory.PowerSeries