import Mathlib

namespace Work.TMC16Core.Basic

theorem exp_arith {k : ℕ} {L ε ε₁ : ℝ}
    (hk : 4 * ((k : ℝ) + 1) * Real.exp (L - ε) < Real.exp ((k : ℝ) * (ε - ε₁))) :
    ((k : ℝ) + 1) * (Real.exp (((k : ℝ) + 1) * (L - ε)) * Real.exp ((k : ℝ) * ε₁))
      < Real.exp ((k : ℝ) * L) / 4 := by
  -- Multiply `hk` by the positive factor `exp (k*(L-ε) + k*ε₁)`.
  have hC : 0 < Real.exp ((k : ℝ) * (L - ε) + (k : ℝ) * ε₁) := Real.exp_pos _
  have h1 := mul_lt_mul_of_pos_right hk hC
  rw [mul_assoc] at h1
  -- Combine the exponentials on both sides.
  rw [← Real.exp_add, ← Real.exp_add] at h1
  have e1 : (L - ε) + ((k : ℝ) * (L - ε) + (k : ℝ) * ε₁)
      = ((k : ℝ) + 1) * (L - ε) + (k : ℝ) * ε₁ := by ring
  have e2 : (k : ℝ) * (ε - ε₁) + ((k : ℝ) * (L - ε) + (k : ℝ) * ε₁)
      = (k : ℝ) * L := by ring
  rw [e1, e2] at h1
  rw [mul_assoc] at h1
  -- Reduce the goal and finish linearly.
  rw [← Real.exp_add]
  linarith

end Work.TMC16Core.Basic
