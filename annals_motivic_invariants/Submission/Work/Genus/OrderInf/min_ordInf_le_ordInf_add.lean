import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.OrderInf

set_option linter.unusedVariables false in
/-- The non-archimedean inequality for the order at infinity.  Unfolds to
`RatFunc.intDegree_add_le` (and `min (-a) (-b) = -max a b`). -/
theorem min_ordInf_le_ordInf_add {F : Type*} [Field F] {f g : RatFunc F} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) :
    min (Work.Genus.ordInf f) (Work.Genus.ordInf g) ≤ Work.Genus.ordInf (f + g) := by
  have h := RatFunc.intDegree_add_le hg hfg
  simp only [Work.Genus.ordInf]
  rw [min_neg_neg]
  exact neg_le_neg h

end Work.Genus.OrderInf
