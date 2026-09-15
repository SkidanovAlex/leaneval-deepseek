import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Real

/-- For any `ε > 0` and `x > 0`, `log x ≤ ε * x - log ε - 1`.
This is the tangent-line (concavity) bound for `log` at the point `1/ε`. -/
theorem log_le_mul_sub_log_sub_one {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ ε * x - Real.log ε - 1 := by
  have h := Real.log_le_sub_one_of_pos (mul_pos hε hx : 0 < ε * x)
  rw [Real.log_mul hε.ne' hx.ne'] at h
  linarith

theorem exists_mul_log_le_mul_self_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → a * Real.log (1 + t) ≤ b * t + B := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · refine ⟨0, fun t ht => ?_⟩
    rw [← ha0, zero_mul]
    nlinarith [mul_nonneg hb.le ht]
  · refine ⟨b - a * Real.log (b / a) - a, fun t ht => ?_⟩
    have hε : 0 < b / a := div_pos hb hapos
    have h1' : 0 < 1 + t := by linarith
    have hlog := log_le_mul_sub_log_sub_one hε h1'
    have hmul : a * Real.log (1 + t)
        ≤ a * ((b / a) * (1 + t) - Real.log (b / a) - 1) :=
      mul_le_mul_of_nonneg_left hlog ha
    have hae : a * (b / a) = b := mul_div_cancel₀ b hapos.ne'
    nlinarith [hmul, hae]

end Commons.Analysis.Real