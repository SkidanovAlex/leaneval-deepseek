import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Central

namespace Commons.NumberTheory.NumberField

open Nat

/-! ### Elementary estimates relating `Nat.log 2 n` and `Real.log n` -/

/-- `Real.log 2 ≥ 1/2`. -/
lemma log_two_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  linarith

/-- For `n ≥ 1`, `Nat.log 2 n ≤ 2 * Real.log n`. -/
lemma cast_nat_log_two_le (n : ℕ) (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  have hn0 : n ≠ 0 := by omega
  have hpow : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn0
  have hpowR : ((2 : ℕ) ^ Nat.log 2 n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpow
  have hLpos : (0 : ℝ) < ((2 : ℕ) ^ Nat.log 2 n : ℝ) := by positivity
  have hlog := Real.log_le_log hLpos hpowR
  have hlog2 : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [Real.log_pow] at hlog
    simpa using hlog
  have hLnn : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
  have hmul : (Nat.log 2 n : ℝ) * ((1 : ℝ) / 2) ≤ (Nat.log 2 n : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left log_two_ge_half hLnn
  linarith [hlog2, hmul]

/-- For `n ≥ 100`, `Real.log n ≥ 4`. -/
lemma four_le_log {n : ℕ} (hn : 100 ≤ n) : (4 : ℝ) ≤ Real.log n := by
  have h64le : (64 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 64 ≤ n by omega)
  have hlog64 : Real.log 64 ≤ Real.log n := Real.log_le_log (by norm_num) h64le
  have h64eq : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have hlog2 : (4 : ℝ) / 6 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [hlog64, h64eq, hlog2]

theorem model_parameters_bounds (n r : ℕ) (hn : 100 ≤ n) (hr2 : Nat.centralBinom r ≤ 16 * n * (r + 1)) (hr4 : r ≤ 2 * (Nat.log 2 n) + 12) : (r : ℝ) ≤ 10 ^ 6 * Real.log n ∧ ((r + r).choose r : ℝ) ≤ 10 ^ 6 * n * Real.log n := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn0 : (0 : ℝ) ≤ n := hnpos.le
  have hlog : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := cast_nat_log_two_le n hn1
  have hlogn4 : (4 : ℝ) ≤ Real.log n := four_le_log hn
  have hr4R : (r : ℝ) ≤ 2 * (Nat.log 2 n : ℝ) + 12 := by exact_mod_cast hr4
  constructor
  · linarith [hr4R, hlog, hlogn4]
  · have hb : (Nat.centralBinom r : ℝ) ≤ 16 * (n : ℝ) * ((r : ℝ) + 1) := by
      exact_mod_cast hr2
    have hr1 : (r : ℝ) + 1 ≤ 2 * (Nat.log 2 n : ℝ) + 13 := by linarith [hr4R]
    have hL4 : 2 * (Nat.log 2 n : ℝ) ≤ 4 * Real.log n := by linarith [hlog]
    have hA : (208 : ℝ) ≤ (10 ^ 6 - 64) * Real.log n := by nlinarith [hlogn4]
    rw [show ((r + r).choose r : ℝ) = (Nat.centralBinom r : ℝ) by
      rw [show r + r = 2 * r by omega, ← Nat.centralBinom_eq_two_mul_choose r]]
    calc (Nat.centralBinom r : ℝ) ≤ 16 * (n : ℝ) * ((r : ℝ) + 1) := hb
      _ ≤ 16 * (n : ℝ) * (2 * (Nat.log 2 n : ℝ) + 13) :=
            mul_le_mul_of_nonneg_left hr1 (by positivity)
      _ ≤ 16 * (n : ℝ) * (4 * Real.log n + 13) :=
            mul_le_mul_of_nonneg_left (by linarith [hL4]) (by positivity)
      _ ≤ 10 ^ 6 * (n : ℝ) * Real.log n := by
            have h := mul_le_mul_of_nonneg_left hA hn0
            nlinarith [h]

end Commons.NumberTheory.NumberField