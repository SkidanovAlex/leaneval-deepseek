import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Family

/-- Every even iterate of the antiholomorphic quadratic `T_c(z) = z̄² + c` is an iterate of the
holomorphic second iterate `Tsq c = T_c ∘ T_c`:  `(T_c)^[2n] = (Tsq c)^[n]`. -/
theorem tantibar_iterate_two_mul (c : ℂ) (n : ℕ) :
    (LeanEval.ComplexAnalysis.Tantibar c)^[2 * n] = (Work.Landing.Tsq c)^[n] := by
  rw [Function.iterate_mul]
  congr 1
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ, Function.iterate_one]
  funext z
  simp only [Function.comp_apply, LeanEval.ComplexAnalysis.Tantibar, Work.Landing.Tsq,
    starRingEnd_apply, star_add, star_pow, star_star]

end Work.Landing.Family
