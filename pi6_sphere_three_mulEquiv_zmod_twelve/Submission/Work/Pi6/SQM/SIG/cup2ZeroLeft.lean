import Mathlib
import Submission.Work.Pi6.SQM.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.SQM.SIG

open Work.Cohomology (Cochain genEval genEval_ext)

/-- **The cup-2 product vanishes with a zero left argument** (cochain level).  Pointwise, the
interval formula `(u ∪₂ v)(σ) = Σ_{a,b} u(σ|U)·v(σ|V)` has every term containing the factor
`genEval F2 X 0 _ = 0`, so `genEval_ext` gives the identity of cochains. -/
theorem cup2ZeroLeft : ∀ (X : SSet) (n m : ℕ) (v : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X m),
    Work.Pi6.SQ.cup2 X n m (0 : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X n) v = 0 := by
  intro X n m v
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Pi6.SQ.genEval_cup2]
  simp only [Work.Cohomology.genEval, LinearMap.zero_apply, zero_mul, Finset.sum_const_zero]

end Work.Pi6.SQM.SIG
