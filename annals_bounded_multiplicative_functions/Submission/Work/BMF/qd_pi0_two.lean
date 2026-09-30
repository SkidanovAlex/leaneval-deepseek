import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For `a ≥ 4` and `a ≤ Q ≤ 2a`, `π₀ Q ≤ 2 π₀ a`.

Here `π₀ P = P / log P`.  Since `log` is increasing and positive on `[4, ∞)`,
`1 / log Q ≤ 1 / log a`, hence `π₀ Q = Q / log Q ≤ Q / log a ≤ 2a / log a = 2 π₀ a`. -/
theorem qd_pi0_two {a Q : ℝ} (ha : 4 ≤ a) (hQ1 : a ≤ Q) (hQ2 : Q ≤ 2 * a) :
    pi0 Q ≤ 2 * pi0 a := by
  have ha0 : 0 < a := by linarith
  have hQpos : 0 < Q := by linarith
  have hlogA : 0 < Real.log a := Real.log_pos (by linarith)
  have hlog : Real.log a ≤ Real.log Q := Real.log_le_log ha0 hQ1
  have h1 : Q / Real.log Q ≤ Q / Real.log a :=
    div_le_div_of_nonneg_left (le_of_lt hQpos) hlogA hlog
  have h2 : Q / Real.log a ≤ 2 * a / Real.log a :=
    div_le_div_of_nonneg_right hQ2 (le_of_lt hlogA)
  rw [pi0, pi0]
  calc Q / Real.log Q ≤ 2 * a / Real.log a := le_trans h1 h2
    _ = 2 * (a / Real.log a) := by ring

end Work.BMF
