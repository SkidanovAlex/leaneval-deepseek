import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `uhsOfHyp` is a left inverse of the upper half space chart `hypOfUHS`

For a point `q` of the upper half space chart,
`hypOfUHS q = (q₀/q₃, q₁/q₃, q₂/q₃, (‖q‖²−1)/(2q₃), (‖q‖²+1)/(2q₃))`, so that its "height
difference" is
`hypOfUHS q 4 - hypOfUHS q 3 = 1/q₃` (this uses `q 3 ≠ 0`, and no sign hypothesis),
while `uhsOfHyp P` is the point `(P₀,P₁,P₂,P₄−P₃)/(P₄−P₃)`.  Composing the two therefore returns
`q`.  This is the formal counterpart of the fact that `hypOfUHS` is injective on the upper half
space `{q : 0 < q 3}`.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-- The height above the hyperboloid of the chart point `hypOfUHS q` is `1/q 3`. -/
theorem hypOfUHS_four_sub_three {q : E4} (hq : q 3 ≠ 0) :
    hypOfUHS q 4 - hypOfUHS q 3 = (q 3)⁻¹ := by
  simp only [hypOfUHS_apply_three, hypOfUHS_apply_four]
  field_simp
  ring

theorem uhsOfHyp_hypOfUHS {q : E4} (hq : q 3 ≠ 0) : uhsOfHyp (hypOfUHS q) = q := by
  ext i
  fin_cases i <;> simp [uhsOfHyp, hypOfUHS] <;> field_simp <;> ring

end Work.HypModel
