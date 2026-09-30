import Mathlib
import Submission.Work.Pi6.SQM.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open CategoryTheory

namespace Work.Pi6.SQM.SIG

/-- The cup-3 product of a zero cochain (on the left) with any cochain vanishes.  This is immediate
from the interval formula `genEval_cup3`: every summand of `cup3Val` is a product of the factor
`genEval F2 X 0 (…)` — which is zero — with `genEval F2 X v (…)`. -/
theorem cup3ZeroLeft : ∀ (X : SSet) (n m : ℕ) (v : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X m),
    Work.Pi6.SQM.cup3 X n m (0 : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X n) v = 0 := by
  intro X n m v
  apply Work.Cohomology.genEval_ext (R := Work.Pi6.SQ.F2) (X := X)
  intro σ
  rw [Work.Pi6.SQM.genEval_cup3]
  simp only [Work.Pi6.SQM.cup3Val, Work.Cohomology.genEval, LinearMap.zero_apply]
  simp

end Work.Pi6.SQM.SIG
