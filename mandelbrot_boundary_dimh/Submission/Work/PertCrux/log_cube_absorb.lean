import Mathlib

namespace Work.PertCrux

/-- Absorbing a cube: if `0 < Y ≤ B^3` and `1 ≤ B`, then `2 + log Y` is at most
`(25/8) * (2 + log B)`.  The cube exponent `3` is beaten by the factor `25/8 > 3`, while
the additive `2` on the right (together with `log B ≥ 0`) covers every remaining case. -/
theorem log_cube_absorb {Y B : ℝ} (hY : 0 < Y) (hB : 1 ≤ B) (hYB : Y ≤ B ^ 3) :
    2 + Real.log Y ≤ (25 / 8) * (2 + Real.log B) := by
  have hlog : Real.log Y ≤ 3 * Real.log B := by
    have h1 : Real.log Y ≤ Real.log (B ^ 3) := Real.log_le_log hY hYB
    rw [Real.log_pow] at h1
    norm_num at h1
    linarith
  have hB0 : 0 ≤ Real.log B := Real.log_nonneg hB
  linarith

end Work.PertCrux
