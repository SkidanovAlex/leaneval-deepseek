import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs

namespace Work.NumberTheory.Chen.BTermCount

/-- `blockCount M Y = Nat.log 2 (Y/M + 1) + 1` is at most `3 log x` for `Y ≤ x`, `x ≥ 8`.

Since `M ≥ 1` we have `Y / M ≤ Y ≤ x`, so the logarithm is bounded by `Nat.log 2 (x+1)`,
which is at most `log₂(x+1) ≤ 2 log(x+1)` because `log 2 ≥ 1/2`; finally the elementary
inequality `2 log(x+1) + 1 ≤ 3 log x` holds for `x ≥ 8` (equivalent to `e·(x+1)² ≤ x³`). -/
theorem blockCountCastLe (x M Y : ℕ) (hx : 8 ≤ x) (hM : 1 ≤ M) (hMY : M ≤ Y) (hY : Y ≤ x) : ((blockCount M Y : ℕ) : ℝ) ≤ 3 * Real.log (x : ℝ) := by
  have hle : Y / M + 1 ≤ x + 1 := by
    have h1 : Y / M ≤ Y := Nat.div_le_self Y M
    omega
  have hlog_mono : Nat.log 2 (Y / M + 1) ≤ Nat.log 2 (x + 1) := Nat.log_mono_right hle
  -- `Real.log 2 ≥ 1/2`
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  -- `2 ^ Nat.log 2 (x+1) ≤ x + 1`, hence after taking logs
  have hk : (2 : ℝ) ^ (Nat.log 2 (x + 1)) ≤ (x : ℝ) + 1 := by
    have h := Nat.pow_log_le_self 2 (by omega : x + 1 ≠ 0)
    have h2 : ((2 : ℕ) ^ Nat.log 2 (x + 1) : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h2
  have hknneg : (0 : ℝ) ≤ (Nat.log 2 (x + 1) : ℕ) := Nat.cast_nonneg _
  have hlogineq : Real.log ((2 : ℝ) ^ Nat.log 2 (x + 1)) ≤ Real.log ((x : ℝ) + 1) :=
    Real.log_le_log (by positivity) hk
  rw [Real.log_pow] at hlogineq
  have hstep2 : (Nat.log 2 (x + 1) : ℝ) ≤ 2 * Real.log ((x : ℝ) + 1) := by
    have hksplit : (Nat.log 2 (x + 1) : ℝ) * (1 / 2)
        ≤ (Nat.log 2 (x + 1) : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2 hknneg
    linarith
  -- elementary real inequality
  have hstep3 : 2 * Real.log ((x : ℝ) + 1) + 1 ≤ 3 * Real.log (x : ℝ) := by
    have hx8 : (8 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hpoly : (3 : ℝ) * ((x : ℝ) + 1) ^ 2 ≤ (x : ℝ) ^ 3 := by
      nlinarith [sq_nonneg ((x : ℝ) - 8), sq_nonneg (x : ℝ), hx8]
    have hexp : Real.exp 1 * ((x : ℝ) + 1) ^ 2 ≤ (x : ℝ) ^ 3 := by
      have h3 : Real.exp 1 * ((x : ℝ) + 1) ^ 2 < 3 * ((x : ℝ) + 1) ^ 2 :=
        mul_lt_mul_of_pos_right Real.exp_one_lt_three (by positivity)
      linarith
    have hLpos : 0 < Real.exp 1 * ((x : ℝ) + 1) ^ 2 := by positivity
    have hlog := Real.log_le_log hLpos hexp
    rw [Real.log_mul (by positivity : Real.exp 1 ≠ 0)
          (by positivity : ((x : ℝ) + 1) ^ 2 ≠ 0),
        Real.log_exp, Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog
    linarith only [hlog]
  unfold blockCount
  push_cast
  calc (Nat.log 2 (Y / M + 1) : ℝ) + 1
      ≤ (Nat.log 2 (x + 1) : ℝ) + 1 := by
        have : (Nat.log 2 (Y / M + 1) : ℝ) ≤ (Nat.log 2 (x + 1) : ℝ) := by
          exact_mod_cast hlog_mono
        linarith
    _ ≤ 2 * Real.log ((x : ℝ) + 1) + 1 := by linarith
    _ ≤ 3 * Real.log (x : ℝ) := hstep3

end Work.NumberTheory.Chen.BTermCount
