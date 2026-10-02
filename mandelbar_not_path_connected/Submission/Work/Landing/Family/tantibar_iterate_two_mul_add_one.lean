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

/-- `(T_c)^[2] = Tsq c`: the holomorphic second iterate `Tsq c` of `Core` is the square of the
antiholomorphic quadratic `T_c(z) = z̄² + c`. -/
theorem tantibar_iterate_two_eq_tsq (c : ℂ) :
    (Tantibar c)^[2] = Work.Landing.Tsq c := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add, Function.iterate_one]
  funext w
  simp [Work.Landing.Tsq, Tantibar]

/-- Odd iterates of the antiholomorphic quadratic are `T_c` followed by iterates of its
holomorphic square: `(T_c)^[2n+1] = T_c ∘ (Tsq c)^[n]`. -/
theorem tantibar_iterate_two_mul_add_one (c : ℂ) (n : ℕ) :
    (LeanEval.ComplexAnalysis.Tantibar c)^[2 * n + 1] =
      LeanEval.ComplexAnalysis.Tantibar c ∘ (Work.Landing.Tsq c)^[n] := by
  funext z
  rw [Function.comp_apply]
  calc (Tantibar c)^[2 * n + 1] z
      = Tantibar c ((Tantibar c)^[2 * n] z) := by
        rw [show 2 * n + 1 = 1 + 2 * n from by ring, Function.iterate_add_apply,
          Function.iterate_one]
    _ = Tantibar c ((Work.Landing.Tsq c)^[n] z) := by
        rw [Function.iterate_mul, tantibar_iterate_two_eq_tsq]

end Work.Landing.Family
