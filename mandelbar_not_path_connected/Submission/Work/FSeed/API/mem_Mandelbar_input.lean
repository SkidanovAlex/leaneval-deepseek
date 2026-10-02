import Mathlib
import Submission.Work.FSeed.Inputs
import Submission.Work.FSeed.Classify
import Submission.Work.FSeed.API.mem_Mandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FSeed.API

/-- **A root-parabolic input parameter lies in the mandelbar.**  `Work.FSeed.Classify` turns the
classical input bundle `Work.FSeed.RootParabolicInput c` into the structure
`Work.EL.RootParabolic c`, and `Work.FSeed.API.mem_Mandelbar` bounds the critical orbit of any
such parameter; composing the two gives membership in the tricorn. -/
theorem mem_Mandelbar_input {c : ℂ} (h : Work.FSeed.RootParabolicInput c) :
    c ∈ LeanEval.ComplexAnalysis.Mandelbar :=
  Work.FSeed.API.mem_Mandelbar (Work.FSeed.rootParabolic_of_input h).some

end Work.FSeed.API
