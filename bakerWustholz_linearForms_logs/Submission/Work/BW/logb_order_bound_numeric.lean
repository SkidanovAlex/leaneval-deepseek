import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! Numeric inequality `log₂(120π·d·log(6d)) + 1 < 120π·log(6d)` for `d ≥ 1`.

Route.  Put `t := Real.log (6*d)`, so `t ≥ 1` (`Real.exp_one_lt_three`, `Real.pi_gt_three`).
`Real.logb` is `Real.log _ / Real.log 2` and `Real.log 2 > 1/2`, so `Real.logb 2 L ≤ 2 * Real.log L`
for `L > 0`.  Split `Real.log L = Real.log (120*π) + Real.log d + Real.log t` and bound the three
terms: `Real.log (120*π) < 10` (`120*π < 1024 = 2^10 < Real.exp 10`, `Real.exp_one_gt_two`),
`Real.log d ≤ t` (as `d ≤ 6*d`), `Real.log t ≤ t - 1 ≤ t` (`Real.log_le_sub_one_of_pos`).
Hence `Real.logb 2 L + 1 < 2*(10 + 2*t) + 1 = 21 + 4*t`, while `120*π*t > 360*t ≥ 21 + 4*t`
because `Real.pi_gt_three` and `t ≥ 1`. -/
theorem logb_order_bound_numeric (d : ℝ) (hd : 1 ≤ d) :
    Real.logb 2 (120 * Real.pi * d * Real.log (6 * d)) + 1
      < 120 * Real.pi * Real.log (6 * d) := by
  have hdpos : 0 < d := by linarith
  -- `t := Real.log (6*d) > 1`, because `6*d ≥ 6 > 3 > Real.exp 1`.
  have ht1 : 1 < Real.log (6 * d) := by
    have h6 : Real.exp 1 < 6 * d := by
      have := Real.exp_one_lt_three
      nlinarith
    have := Real.log_lt_log (Real.exp_pos 1) h6
    rwa [Real.log_exp] at this
  have htpos : 0 < Real.log (6 * d) := by linarith
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  -- exact splitting of `log L`
  have hlogL : Real.log (120 * Real.pi * d * Real.log (6 * d))
      = Real.log (120 * Real.pi) + Real.log d + Real.log (Real.log (6 * d)) := by
    rw [Real.log_mul (by positivity) (ne_of_gt htpos),
        Real.log_mul (by positivity) (ne_of_gt hdpos)]
  -- `log (120π) < 10`, since `120π < 480 < 1024 = 2^10 < exp 10`.
  have h120 : Real.log (120 * Real.pi) < 10 := by
    have hexp10 : (1024 : ℝ) < Real.exp 10 := by
      have h2 : (2:ℝ) < Real.exp 1 := Real.exp_one_gt_two
      have hp : (2:ℝ)^10 < (Real.exp 1)^10 := pow_lt_pow_left₀ h2 (by norm_num) (by norm_num)
      rw [← Real.exp_nat_mul] at hp
      norm_num at hp ⊢
      exact hp
    rw [Real.log_lt_iff_lt_exp (by positivity : (0:ℝ) < 120 * Real.pi)]
    linarith [Real.pi_lt_four, hexp10]
  -- `log L < 10 + 2*t`
  have hlogL_ub : Real.log (120 * Real.pi * d * Real.log (6 * d))
      < 10 + 2 * Real.log (6 * d) := by
    rw [hlogL]
    have h1 := Real.log_le_sub_one_of_pos htpos
    have h2 : Real.log d ≤ Real.log (6 * d) := Real.log_le_log hdpos (by linarith)
    linarith
  -- `21 + 4*t < 120π*t`
  have hbig : 21 + 4 * Real.log (6 * d) < 120 * Real.pi * Real.log (6 * d) := by
    have hp := Real.pi_gt_three
    have ht := le_of_lt ht1
    nlinarith
  have hft : 2 * Real.log (120 * Real.pi * d * Real.log (6 * d)) + 1
      < 120 * Real.pi * Real.log (6 * d) := by linarith
  have hLgt1 : 1 < 120 * Real.pi * d * Real.log (6 * d) := by
    have hp := Real.pi_gt_three
    nlinarith [hd, ht1]
  have hlogLpos : 0 < Real.log (120 * Real.pi * d * Real.log (6 * d)) := Real.log_pos hLgt1
  -- `log L / log 2 < 2 * log L`
  have hdiv : Real.log (120 * Real.pi * d * Real.log (6 * d)) / Real.log 2
      < 2 * Real.log (120 * Real.pi * d * Real.log (6 * d)) := by
    rw [div_lt_iff₀ (by linarith : 0 < Real.log 2)]
    nlinarith [hlog2, hlogLpos]
  simp only [Real.logb]
  linarith

end Work.BW
