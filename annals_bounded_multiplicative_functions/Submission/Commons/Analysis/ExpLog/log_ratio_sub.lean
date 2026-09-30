import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.ExpLog

/-! For `0 < b ≤ a`: `log(a/b) ≥ (a−b)/a`.
A complete proof already exists in `Submission/ChildDirichletMV.lean`
(`Submission.BoundedMultiplicativeFunctions.log_ratio_sub`). -/
lemma log_ratio_sub (a b : ℝ) (hb : 0 < b) (hab : b ≤ a) :
    Real.log (a / b) ≥ (a - b) / a := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hpos : 0 < a / b := div_pos ha hb
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hrew : 1 - (a / b)⁻¹ = (a - b) / a := by
    field_simp [ha.ne', hb.ne']
  rwa [hrew] at h

end Commons.Analysis.ExpLog