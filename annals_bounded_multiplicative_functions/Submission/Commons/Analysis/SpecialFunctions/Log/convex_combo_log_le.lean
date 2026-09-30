import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.SpecialFunctions.Log

theorem convex_combo_log_le (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * Real.log a + t * Real.log b ≤ Real.log ((1 - t) * a + t * b) := by
  have hw1 : 0 ≤ 1 - t := by linarith
  have hsum : (1 - t) + t = 1 := by ring
  exact (strictConcaveOn_log_Ioi.concaveOn).2 ha hb hw1 ht0 hsum

end Commons.Analysis.SpecialFunctions.Log