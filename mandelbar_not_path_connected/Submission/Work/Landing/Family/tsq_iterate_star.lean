import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Family

/-- `Tsq c` intertwines complex conjugation with `Tsq (star c)`:
`Tsq c (star z) = star (Tsq (star c) z)`. -/
lemma Tsq_star (c z : ℂ) : Work.Landing.Tsq c (star z) = star (Work.Landing.Tsq (star c) z) := by
  simp [Work.Landing.Tsq, star_pow]

/-- Iterated form of `Tsq_star`. -/
theorem tsq_iterate_star (c z : ℂ) (n : ℕ) :
    (Work.Landing.Tsq c)^[n] (star z) = star ((Work.Landing.Tsq (star c))^[n] z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Tsq_star, Function.iterate_succ_apply']

end Work.Landing.Family
