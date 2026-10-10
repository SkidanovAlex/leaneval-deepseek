import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.OrderInf

/-- The order at infinity is additive on quotients of non-zero functions.  Immediate from
`RatFunc.intDegree_div`. -/
theorem ordInf_div {F : Type*} [Field F] {f g : RatFunc F} (hf : f ≠ 0) (hg : g ≠ 0) :
    Work.Genus.ordInf (f / g) = Work.Genus.ordInf f - Work.Genus.ordInf g := by
  simp only [Work.Genus.ordInf, RatFunc.intDegree_div hf hg]
  first | refl_ring1 | ring

end Work.Genus.OrderInf
