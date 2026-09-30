import Mathlib
import Submission.Work.BMF.VKdenom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VK

/-! ### Numerical inputs

We record the two elementary exponential estimates used to bound `Real.log 6` and
`Real.log (Real.log 6)` from below. -/

lemma exp_half_lt_two : Real.exp (1 / 2 : ℝ) < 2 := by
  have h : (Real.exp (1 / 2 : ℝ)) ^ 2 < (2 : ℝ) ^ 2 := by
    rw [← Real.exp_nat_mul (1 / 2 : ℝ) 2]
    norm_num
    linarith [Real.exp_one_lt_three]
  rw [pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)] at h
  exact h

lemma exp_three_halves_le_six : Real.exp (3 / 2 : ℝ) ≤ 6 := by
  have h : Real.exp (3 / 2 : ℝ) = Real.exp 1 * Real.exp (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.exp_add]
  rw [h]
  nlinarith [Real.exp_one_lt_three, exp_half_lt_two, Real.exp_pos (1 / 2 : ℝ),
    Real.exp_pos (1 : ℝ)]

lemma exp_quarter_lt_three_halves : Real.exp (1 / 4 : ℝ) < 3 / 2 := by
  have h : (Real.exp (1 / 4 : ℝ)) ^ 4 < (3 / 2 : ℝ) ^ 4 := by
    rw [← Real.exp_nat_mul (1 / 4 : ℝ) 4]
    norm_num
    linarith [Real.exp_one_lt_three]
  rw [pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)] at h
  exact h

lemma half_le_quarter_rpow_third : (1 / 2 : ℝ) ≤ (1 / 4 : ℝ) ^ (1 / 3 : ℝ) := by
  have hcube : ((1 / 4 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = 1 / 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    norm_num
  have key : ((1 / 2 : ℝ)) ^ 3 ≤ ((1 / 4 : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
    rw [hcube]; norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0)
    (Real.rpow_nonneg (by norm_num) _) key

/-- `VKd 6 ≥ 1/2`, the base point of the lower bound. -/
lemma VKd_six_ge_half : (1 / 2 : ℝ) ≤ Work.BMF.VKd 6 := by
  rw [Work.BMF.VKd_def]
  set L : ℝ := Real.log 6 with hL
  have hL32 : (3 / 2 : ℝ) ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 6)]
    exact exp_three_halves_le_six
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have h1 : (1 : ℝ) ≤ L ^ (2 / 3 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hlogL : (1 / 4 : ℝ) ≤ Real.log L := by
    have h4 : Real.exp (1 / 4 : ℝ) ≤ L := le_of_lt (lt_of_lt_of_le exp_quarter_lt_three_halves hL32)
    have := Real.log_le_log (Real.exp_pos (1 / 4 : ℝ)) h4
    rwa [Real.log_exp] at this
  have h2 : (1 / 4 : ℝ) ^ (1 / 3 : ℝ) ≤ (Real.log L) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hlogL (by norm_num)
  have hprod : (1 : ℝ) * (1 / 4 : ℝ) ^ (1 / 3 : ℝ) ≤
      L ^ (2 / 3 : ℝ) * (Real.log L) ^ (1 / 3 : ℝ) :=
    mul_le_mul h1 h2 (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by linarith) _)
  linarith [hprod, half_le_quarter_rpow_third]

/-- **Numerical lower bound for the Vinogradov–Korobov denominator.**

For `y ≥ 6` one has `1/2 ≤ VKd y`, where `VKd y = (log y)^{2/3} (log log y)^{1/3}`
(`Work.BMF.VKd`, `Submission/Work/BMF/VKdenom.lean`).  Equivalently `VKd (|t|+3) ≥ 1/2` for
`|t| ≥ 3`.

Route: put `ℓ = Real.log y ≥ Real.log 6 > 3/2`, so `ℓ^(2/3) ≥ 1`; and `Real.log ℓ ≥ 1/4`
because `ℓ > 3/2`.  Hence `VKd y ≥ 1 * (1/4)^(1/3) ≥ 1/2`.  The two numerical inputs reduce to
`Real.exp (3/2) ≤ 6` (i.e. `Real.exp 1 < 3` and `Real.exp (1/2) < 2`) and
`Real.exp (1/4) ≤ 3/2` (from `(3/2)^4 = 81/16 > 3 > Real.exp 1`); `Real.log_two_gt_d9` is also
available.  Everything is `Real.rpow_le_rpow` / `Real.log_le_log` bookkeeping. -/
theorem VKd_ge_half {y : ℝ} (hy : 6 ≤ y) : (1 / 2 : ℝ) ≤ Work.BMF.VKd y :=
  le_trans VKd_six_ge_half (Work.BMF.VKd_mono (by norm_num) hy)

end Work.BMF.VK
