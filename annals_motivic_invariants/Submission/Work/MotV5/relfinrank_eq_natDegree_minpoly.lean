import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

theorem relfinrank_eq_natDegree_minpoly {K E : Type*} [Field K] [Field E] [Algebra K E]
    {F B : IntermediateField K E} {x : E} (hFB : F ≤ B)
    (hB : B = IntermediateField.restrictScalars K (IntermediateField.adjoin F {x}))
    (hx : IsIntegral F x) :
    F.relfinrank B = (minpoly F x).natDegree := by
  subst hB
  rw [IntermediateField.relfinrank_eq_finrank_of_le hFB]
  have heq : IntermediateField.extendScalars hFB = IntermediateField.adjoin (↥F) {x} := by
    ext y
    rw [IntermediateField.mem_extendScalars]
    exact Iff.rfl
  rw [heq, IntermediateField.adjoin.finrank hx]

end Work.MotV5
