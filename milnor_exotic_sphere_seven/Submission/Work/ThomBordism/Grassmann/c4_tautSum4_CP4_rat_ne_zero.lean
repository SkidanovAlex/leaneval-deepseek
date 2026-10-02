import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.p1RatAux
import Submission.Work.ThomBordism.Grassmann.c4Aux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Grassmann

/-- The proof is in `Work.ThomBordism.Grassmann.c4_tautSum4_rat_ne_zero_aux`: the bundle of the
statement is definitionally `tautSum4 = lineC 4 ⊕ lineC 4`. -/
theorem c4_tautSum4_CP4_rat_ne_zero :
    (1 : ℚ) ⊗ₜ[ℤ] (Work.Thom.chernClass 4 4
        (Work.Whitney.whitneySum
          (Work.Whitney.whitneySum (Work.Gen.tautDual 4) (Work.Gen.tautLine 4))
          (Work.Whitney.whitneySum (Work.Gen.tautDual 4) (Work.Gen.tautLine 4)))) ≠ 0 := by
  show (1 : ℚ) ⊗ₜ[ℤ] (Work.Thom.chernClass 4 4 tautSum4) ≠ 0
  exact c4_tautSum4_rat_ne_zero_aux

end Work.ThomBordism.Grassmann
