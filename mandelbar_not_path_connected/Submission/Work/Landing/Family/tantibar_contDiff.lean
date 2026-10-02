import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Family

open LeanEval.ComplexAnalysis (Tantibar)

/-- Complex conjugation, viewed as a real continuous linear map, is `ContDiff` in the
real sense at every order. -/
theorem contDiff_starRingEnd (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun z : ℂ => star z) := by
  rw [show (fun z : ℂ => star z) = ⇑Complex.conjCLE from
    funext (fun z => (Complex.conjCLE_apply z).symm)]
  exact Complex.conjCLE.contDiff

/-- The mandelbar iterator `T_c(z) = z̄² + c` is real-smooth at every order: it is the sum
of a constant and the composition of the (real-)smooth squaring map on `ℂ` with complex
conjugation, which is a real continuous linear equivalence. -/
theorem tantibar_contDiff (c : ℂ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (LeanEval.ComplexAnalysis.Tantibar c) := by
  unfold Tantibar
  exact ((contDiff_starRingEnd n).pow 2).add contDiff_const

end Work.Landing.Family
