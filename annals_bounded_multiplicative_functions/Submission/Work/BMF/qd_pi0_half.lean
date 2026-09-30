import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Since `π₀(P) = P / log P` is increasing on `(e, ∞)` and `a/2 ≤ Q ≤ a` with `a ≥ 4`,
we have `π₀ Q ≤ π₀ a ≤ 2 π₀ a`, hence `π₀ Q ^ 2 ≤ 4 π₀ a ^ 2`. -/
theorem qd_pi0_half {a Q : ℝ} (ha : 4 ≤ a) (hQ1 : a / 2 ≤ Q) (hQ2 : Q ≤ a) :
    pi0 Q ^ 2 ≤ 4 * pi0 a ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hQpos : 0 < Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hlogA : 0 < Real.log a := Real.log_pos (by linarith)
  have hlogHalf : 0 < Real.log (a / 2) := Real.log_pos (by linarith)
  -- `Q / log Q ≤ a / log Q`
  have hstep1 : Q / Real.log Q ≤ a / Real.log Q :=
    div_le_div_of_nonneg_right hQ2 (le_of_lt hlogQ)
  -- `a / log Q ≤ a / log (a/2)`
  have hstep2 : a / Real.log Q ≤ a / Real.log (a / 2) :=
    div_le_div_of_nonneg_left (le_of_lt ha0) hlogHalf
      (Real.log_le_log (by linarith) hQ1)
  -- `log a ≤ 2 log (a/2)`
  have hla : Real.log a ≤ 2 * Real.log (a / 2) := by
    have h4 : Real.log 4 ≤ Real.log a := Real.log_le_log (by norm_num) ha
    have hsplit : Real.log (a / 2) = Real.log a - Real.log 2 :=
      Real.log_div (ne_of_gt ha0) (by norm_num)
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      have h4eq : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [h4eq, Real.log_pow]
      norm_num
    linarith
  -- `a / log (a/2) ≤ 2 a / log a`
  have hstep3 : a / Real.log (a / 2) ≤ 2 * a / Real.log a := by
    rw [div_le_div_iff₀ hlogHalf hlogA]
    nlinarith [hla, le_of_lt ha0]
  have hchain : pi0 Q ≤ 2 * pi0 a := by
    rw [pi0, pi0]
    calc Q / Real.log Q ≤ 2 * a / Real.log a := le_trans hstep1 (le_trans hstep2 hstep3)
      _ = 2 * (a / Real.log a) := by rw [mul_div_assoc]
  have hnnQ : 0 ≤ pi0 Q := by
    rw [pi0]; exact div_nonneg (le_of_lt hQpos) (le_of_lt hlogQ)
  calc pi0 Q ^ 2 ≤ (2 * pi0 a) ^ 2 := pow_le_pow_left₀ hnnQ hchain 2
    _ = 4 * pi0 a ^ 2 := by ring

end Work.BMF
