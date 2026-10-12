import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FockBridge

theorem convexOn_inv_Ioi : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => x⁻¹) := by
  have h := strictConvexOn_zpow (m := -1) (by norm_num) (by norm_num)
  simpa [zpow_neg_one] using h.convexOn

end Work.FockBridge
