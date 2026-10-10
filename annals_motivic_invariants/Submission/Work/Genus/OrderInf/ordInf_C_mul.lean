import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.OrderInf

/-- Multiplication by a non-zero constant does not change the order at infinity.  (`RatFunc.algebraMap_eq_C`,
`RatFunc.intDegree_C`, `RatFunc.intDegree_mul`; the case `f = 0` is immediate since both sides are
`0`.) -/
theorem ordInf_C_mul {F : Type*} [Field F] {c : F} (hc : c ≠ 0) (f : RatFunc F) :
    Work.Genus.ordInf (algebraMap F (RatFunc F) c * f) = Work.Genus.ordInf f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [Work.Genus.ordInf]
  · have hC : algebraMap F (RatFunc F) c ≠ 0 := by
      simpa using (RatFunc.C_injective (K := F)).ne hc
    rw [Work.Genus.ordInf, Work.Genus.ordInf, RatFunc.intDegree_mul hC hf]
    simp [RatFunc.algebraMap_eq_C]

end Work.Genus.OrderInf
