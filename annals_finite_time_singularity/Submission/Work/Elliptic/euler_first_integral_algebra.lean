import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

/-- First-integral algebra identity: given `α ≠ 0`, `α * c = 5 + α` and
`α * z * w + (5 + α) * v = 0`, together with `0 < z`, one gets
`c * z^(c-1) * v + z^c * w = 0`. -/
lemma euler_first_integral_algebra (α c z v w : ℝ) (hz : 0 < z) (hα : α ≠ 0)
    (hc : α * c = 5 + α) (hzw : α * z * w + (5 + α) * v = 0) :
    c * z ^ (c - 1) * v + z ^ c * w = 0 := by
  have hcvw : c * v + z * w = 0 := by
    have hmul : α * (z * w + c * v) = 0 := by
      linear_combination hzw + v * hc
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hα
    · linarith
  have hrpow : z ^ c = z ^ (c - 1) * z := by
    have h := Real.rpow_add hz (c - 1) 1
    rw [show (c - 1) + 1 = c by ring, Real.rpow_one] at h
    exact h
  rw [hrpow]
  linear_combination z ^ (c - 1) * hcvw

end Work.Elliptic
