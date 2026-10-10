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

/-- The order at infinity (`Work.Genus.ordInf f = -f.intDegree`, positive = pole at infinity) is
additive on products.  Immediate from `RatFunc.intDegree_mul`. -/
theorem ordInf_mul {F : Type*} [Field F] {f g : RatFunc F} (hf : f ≠ 0) (hg : g ≠ 0) :
    Work.Genus.ordInf (f * g) = Work.Genus.ordInf f + Work.Genus.ordInf g := by
  rw [Work.Genus.ordInf, RatFunc.intDegree_mul hf hg, Work.Genus.ordInf, Work.Genus.ordInf]
  first | refl_ring1 | ring

end Work.Genus.OrderInf
