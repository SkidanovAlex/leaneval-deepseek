import Mathlib
import Submission.Work.Fx.LogTwoDefs

/-!
# Elementary bounds for the `log 2` fixed-point development

* `logS_le_pow`: the running sum never exceeds the scale `2^logP p`.
* the `isz ≤ logSZ p` bounds for every value that occurs in the loop.
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- Telescoping bound: `Σ_{n<k} 2^P/2^(n+1) + 2^P/2^k ≤ 2^P`. -/
theorem sum_div_pow_add_le (P k : ℕ) :
    (∑ n ∈ Finset.range k, 2 ^ P / 2 ^ (n + 1)) + 2 ^ P / 2 ^ k ≤ 2 ^ P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hstep : 2 ^ P / 2 ^ (k + 1) + 2 ^ P / 2 ^ (k + 1) ≤ 2 ^ P / 2 ^ k := by
      have h : 2 ^ P / 2 ^ (k + 1) = (2 ^ P / 2 ^ k) / 2 := by
        rw [pow_succ, Nat.div_div_eq_div_mul]
      rw [h]
      have := Nat.div_add_mod (2 ^ P / 2 ^ k) 2
      omega
    have := Nat.add_le_add_left hstep (∑ n ∈ Finset.range k, 2 ^ P / 2 ^ (n + 1))
    calc (∑ n ∈ Finset.range k, 2 ^ P / 2 ^ (n + 1)) + 2 ^ P / 2 ^ (k + 1) + 2 ^ P / 2 ^ (k + 1)
        = (∑ n ∈ Finset.range k, 2 ^ P / 2 ^ (n + 1)) +
            (2 ^ P / 2 ^ (k + 1) + 2 ^ P / 2 ^ (k + 1)) := by ring
      _ ≤ (∑ n ∈ Finset.range k, 2 ^ P / 2 ^ (n + 1)) + 2 ^ P / 2 ^ k := this
      _ ≤ 2 ^ P := ih

/-- The running sum stays below the scale. -/
theorem logS_le_pow (p k : ℕ) : logS p k ≤ 2 ^ logP p := by
  have h1 : logS p k ≤ ∑ j ∈ Finset.range k, 2 ^ logP p / 2 ^ (j + 1) := by
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [logS, logA, logD]
    exact Nat.div_le_self _ _
  have h2 : (∑ j ∈ Finset.range k, 2 ^ logP p / 2 ^ (j + 1)) ≤ 2 ^ logP p :=
    le_trans (Nat.le_add_right _ _) (sum_div_pow_add_le (logP p) k)
  exact le_trans h1 h2

theorem logD_isz_le (p i : ℕ) : isz ((logD p i : ℕ) : ℤ) ≤ logSZ p := by
  have h1 : logD p i < 2 ^ (2 * p + 22) := by
    have := logD_le_pow p i
    have h2 : logP p < 2 * p + 22 := by simp only [logP]; omega
    exact lt_of_le_of_lt this (Nat.pow_lt_pow_right (by norm_num) h2)
  have h3 : (logD p i).size ≤ 2 * p + 22 := Nat.size_le.mpr h1
  simp only [isz, Int.natAbs_natCast, logSZ]
  omega

theorem logS_isz_le (p i : ℕ) : isz ((logS p i : ℕ) : ℤ) ≤ logSZ p := by
  have h1 : logS p i < 2 ^ (2 * p + 22) := by
    have := logS_le_pow p i
    have h2 : logP p < 2 * p + 22 := by simp only [logP]; omega
    exact lt_of_le_of_lt this (Nat.pow_lt_pow_right (by norm_num) h2)
  have h3 : (logS p i).size ≤ 2 * p + 22 := Nat.size_le.mpr h1
  simp only [isz, Int.natAbs_natCast, logSZ]
  omega

theorem logM_isz_le (p : ℕ) : isz ((logM p : ℕ) : ℤ) ≤ logSZ p := by
  have h1 : logM p < 2 ^ (2 * p + 22) := by
    simp only [logM]
    exact lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
      |>.trans_le (le_refl _)
  have h3 : (logM p).size ≤ 2 * p + 22 := Nat.size_le.mpr h1
  simp only [isz, Int.natAbs_natCast, logSZ]
  omega

theorem p_isz_le (p : ℕ) : isz ((p : ℕ) : ℤ) ≤ logSZ p := by
  have h1 : p < 2 ^ (2 * p + 22) := by
    have h2 : p ≤ 2 * p + 22 := by omega
    exact lt_of_le_of_lt h2 (Nat.lt_two_pow_self)
  have h3 : p.size ≤ 2 * p + 22 := Nat.size_le.mpr h1
  simp only [isz, Int.natAbs_natCast, logSZ]
  omega

theorem idx_isz_le (p i : ℕ) (h : i ≤ logM p + 1) : isz ((i : ℕ) : ℤ) ≤ logSZ p := by
  have h1 : i < 2 ^ (2 * p + 22) := by
    have h2 : i ≤ 2 * p + 22 := by simp only [logM] at h; omega
    exact lt_of_le_of_lt h2 (Nat.lt_two_pow_self)
  have h3 : i.size ≤ 2 * p + 22 := Nat.size_le.mpr h1
  simp only [isz, Int.natAbs_natCast, logSZ]
  omega

end Work.Fx
