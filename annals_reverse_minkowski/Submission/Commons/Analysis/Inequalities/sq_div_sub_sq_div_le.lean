import Mathlib

namespace Commons.Analysis.Inequalities

/-- Elementary convexity inequality used in the induction step of the Brascamp–Lieb inequality
(Carlen–Cordero-Erausquin–Lieb, appendix): for `0 < β < α` and reals `a b`,
`a²/α - b²/β ≤ (a-b)²/(α-β)`.  Proof: multiply by `αβ(α-β) > 0`; the difference becomes
`(aβ - bα)² ≥ 0`. -/
theorem sq_div_sub_sq_div_le {a b α β : ℝ} (hβ : 0 < β) (hβα : β < α) :
    a ^ 2 / α - b ^ 2 / β ≤ (a - b) ^ 2 / (α - β) := by
  have hα : 0 < α := lt_trans hβ hβα
  have hαβ : 0 < α - β := sub_pos.mpr hβα
  have hfac : 0 < α * β * (α - β) := by positivity
  have hdiff : (a - b) ^ 2 / (α - β) - (a ^ 2 / α - b ^ 2 / β)
      = (a * β - b * α) ^ 2 / (α * β * (α - β)) := by
    field_simp
    ring
  rw [← sub_nonneg, hdiff]
  positivity

end Commons.Analysis.Inequalities
