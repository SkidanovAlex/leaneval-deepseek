import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The calculus step of BW (13): `h(1 + log(1 + x/h)) ≤ h (log μ + 2/μ) + x/μ` for `h, μ > 0`, `x ≥ 0` (maximise `log(1+u) - u/μ` at `u = x/h`). -/
theorem est14_thetaopt {mu h x : ℝ} (hmu : 0 < mu) (hh : 0 < h) (hx : 0 ≤ x) :
    h * (1 + Real.log (1 + x / h)) ≤ h * (Real.log mu + 2 / mu) + x / mu := by
  have h1u : 0 < 1 + x / h := by positivity
  -- Apply the tangent-line bound `log z ≤ z - 1` at `z = (1 + x/h)/μ`:
  -- `log(1 + x/h) - log μ ≤ (1 + x/h)/μ - 1 ≤ x/h/μ + 2/μ - 1`.
  have hlog : Real.log (1 + x / h) ≤ Real.log mu + 2 / mu + x / h / mu - 1 := by
    have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 + x / h) / mu by positivity)
    rw [Real.log_div (ne_of_gt h1u) (ne_of_gt hmu)] at hl
    have hle : (1 + x / h) / mu - 1 ≤ 2 / mu + x / h / mu - 1 := by
      have hEq : (1 + x / h) / mu = 1 / mu + x / h / mu := by field_simp
      rw [hEq]
      have h2 : 1 / mu ≤ 2 / mu := by
        rw [div_le_div_iff_of_pos_right hmu]; norm_num
      linarith
    linarith
  have key : 1 + Real.log (1 + x / h) ≤ Real.log mu + 2 / mu + x / h / mu := by linarith
  calc h * (1 + Real.log (1 + x / h)) ≤ h * (Real.log mu + 2 / mu + x / h / mu) :=
        mul_le_mul_of_nonneg_left key (le_of_lt hh)
    _ = h * (Real.log mu + 2 / mu) + x / mu := by field_simp

end Work.BW
