import Mathlib.Data.ENNReal.Operations

namespace Commons.Analysis.ENNReal

theorem mul_le_mul_left_iff {a b c : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    c * a ≤ c * b ↔ a ≤ b := by
  simpa [mul_comm] using ENNReal.mul_le_mul_iff_left (a := a) (b := b) (c := c) hc0 hct

end Commons.Analysis.ENNReal