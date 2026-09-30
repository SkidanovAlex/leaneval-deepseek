import Mathlib
import Submission.Work.BMF.Psi1_local_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Decay of `serTerm` for blocks `k` above the block `j` of `p`

For `j ≤ k` the block index `k` lies at or above `j`, so `|j - k| = k - j`.  The
kernel factor `exp (-(log 2)^2 * (max 0 (|j - k| - 1))^2)` of `serTerm` is then
controlled by `exp (-1/8)^(k - j)`, and the loss of `2^(-k α)` compared with
`2^(-j α)` is absorbed by the explicit factor `10`.  This is the mirror image of
`Work.BMF.serTerm_le_of_le`.
-/

namespace Work.BMF

/-- `exp (-1/8) ≥ 7/8`, from the elementary lower bound `1 + x ≤ exp x`. -/
lemma exp_neg_eighth_ge_seven_eighths : (7 / 8 : ℝ) ≤ Real.exp (-(1 / 8 : ℝ)) := by
  have h := Real.add_one_le_exp (-(1 / 8 : ℝ))
  linarith

/-- For `d ≥ 2`, `((d : ℝ) - 1)^2 ≥ d / 2`. -/
lemma sq_pred_ge_half (d : ℕ) (hd : 2 ≤ d) : (d : ℝ) / 2 ≤ ((d : ℝ) - 1) ^ 2 := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (d : ℝ) - 2 by linarith)
    (show (0 : ℝ) ≤ 2 * (d : ℝ) - 1 by linarith)]

/-- The kernel factor of `serTerm` at distance `d = k - j` is bounded by
`10 * exp (-1/8)^d`.  For `d ≤ 1` the left side is `1` (a constant `10` is more than
enough); for `d ≥ 2` the quadratic exponent `(log 2)^2 (d - 1)^2` dominates `d / 8`,
using `log 2 ≥ 1/2`. -/
lemma dyadic_max_exp_bound (d : ℕ) :
    Real.exp (-(Real.log 2) ^ 2 * (max 0 ((d : ℝ) - 1)) ^ 2) ≤
      10 * (Real.exp (-(1 / 8 : ℝ))) ^ d := by
  by_cases hd1 : d ≤ 1
  · have hd01 : d = 0 ∨ d = 1 := by omega
    rcases hd01 with h | h
    · subst h
      have hz : max 0 (((0 : ℕ) : ℝ) - 1) = 0 := by norm_num
      rw [hz]
      norm_num
    · subst h
      have hz : max 0 (((1 : ℕ) : ℝ) - 1) = 0 := by norm_num
      rw [hz]
      have h7 := exp_neg_eighth_ge_seven_eighths
      have he := Real.exp_pos (-(1 / 8 : ℝ))
      norm_num
      nlinarith
  · have hd2 : 2 ≤ d := by omega
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    have hsq : (d : ℝ) / 2 ≤ ((d : ℝ) - 1) ^ 2 := sq_pred_ge_half d hd2
    have hlog : (1 / 4 : ℝ) ≤ (Real.log 2) ^ 2 := by
      have h1 := half_le_log_two
      have h2 := log_two_pos
      nlinarith
    have hprod : (d : ℝ) / 8 ≤ (Real.log 2) ^ 2 * ((d : ℝ) - 1) ^ 2 := by
      calc (d : ℝ) / 8 = (1 / 4) * ((d : ℝ) / 2) := by ring
        _ ≤ (Real.log 2) ^ 2 * ((d : ℝ) - 1) ^ 2 :=
            mul_le_mul hlog hsq (by linarith) (sq_nonneg _)
    have hmax : max 0 ((d : ℝ) - 1) = (d : ℝ) - 1 := by
      apply max_eq_right
      linarith
    have hexp : Real.exp (-(Real.log 2) ^ 2 * (max 0 ((d : ℝ) - 1)) ^ 2) ≤
        (Real.exp (-(1 / 8 : ℝ))) ^ d := by
      rw [hmax]
      rw [show (Real.exp (-(1 / 8 : ℝ))) ^ d = Real.exp (-(1 / 8 : ℝ) * (d : ℝ)) by
        rw [show -(1 / 8 : ℝ) * (d : ℝ) = (d : ℝ) * (-(1 / 8 : ℝ)) by ring,
          Real.exp_nat_mul]]
      apply Real.exp_le_exp.mpr
      linarith
    have hnn : (0 : ℝ) ≤ (Real.exp (-(1 / 8 : ℝ))) ^ d :=
      pow_nonneg (le_of_lt (Real.exp_pos _)) d
    linarith

theorem serTerm_le_of_ge (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) {j k : ℕ} (hk : j ≤ k) :
    Work.BMF.serTerm α j k ≤
      10 * (2 : ℝ) ^ (-(j : ℝ) * α) * (Real.exp (-(1 / 8 : ℝ))) ^ (k - j) := by
  have hjk : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have habs : |(j : ℝ) - (k : ℝ)| = ((k - j : ℕ) : ℝ) := by
    rw [abs_of_nonpos (by linarith : (j : ℝ) - (k : ℝ) ≤ 0), Nat.cast_sub hk]
    ring
  rw [serTerm, habs]
  have h1 : (2 : ℝ) ^ (-(k : ℝ) * α) ≤ (2 : ℝ) ^ (-(j : ℝ) * α) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by nlinarith [mul_le_mul_of_nonneg_right hjk (le_of_lt hα0)])
  have h2 := dyadic_max_exp_bound (k - j)
  calc (2 : ℝ) ^ (-(k : ℝ) * α) *
        Real.exp (-(Real.log 2) ^ 2 * (max 0 (((k - j : ℕ) : ℝ) - 1)) ^ 2)
      ≤ (2 : ℝ) ^ (-(j : ℝ) * α) *
        Real.exp (-(Real.log 2) ^ 2 * (max 0 (((k - j : ℕ) : ℝ) - 1)) ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ ≤ (2 : ℝ) ^ (-(j : ℝ) * α) * (10 * (Real.exp (-(1 / 8 : ℝ))) ^ (k - j)) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by norm_num) _)
    _ = 10 * (2 : ℝ) ^ (-(j : ℝ) * α) * (Real.exp (-(1 / 8 : ℝ))) ^ (k - j) := by ring

end Work.BMF
