import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Q2PR

/-- For every positive real `c` the quadratic equation `c s² - s - 1 = 0` has a real root:
namely `s = (1 + √(1 + 4c)) / (2c)`. -/
theorem quad_root_real (c : ℝ) (hc : 0 < c) : ∃ s : ℝ, c * s ^ 2 - s - 1 = 0 := by
  set d := Real.sqrt (1 + c * 4) with hd
  have hsq : d ^ 2 = 1 + c * 4 := by rw [hd]; exact Real.sq_sqrt (by linarith)
  refine ⟨(1 + d) / (2 * c), ?_⟩
  have hc0 : c ≠ 0 := ne_of_gt hc
  field_simp
  ring_nf
  nlinarith [hsq]

end Work.Diff.Alg.Q2PR
