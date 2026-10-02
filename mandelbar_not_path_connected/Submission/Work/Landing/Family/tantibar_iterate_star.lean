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

/-- The step identity behind `tantibar_iterate_star`: conjugating before applying the
mandelbar iterator is the same as conjugating after applying the iterator with conjugated
parameter. -/
private lemma tantibar_star_step (c z : ℂ) :
    Tantibar c (star z) = star (Tantibar (star c) z) := by
  simp only [Tantibar]
  simp

theorem tantibar_iterate_star (c z : ℂ) (n : ℕ) :
    (LeanEval.ComplexAnalysis.Tantibar c)^[n] (star z) =
      star ((LeanEval.ComplexAnalysis.Tantibar (star c))^[n] z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact tantibar_star_step c _

end Work.Landing.Family
