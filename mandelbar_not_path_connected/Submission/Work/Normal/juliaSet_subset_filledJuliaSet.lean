import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.Frontier
import Submission.Work.Normal.JuliaBasics

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normal

open Set

/-- The Julia set of a polynomial map of degree at least two is contained in the filled Julia set,
being the boundary of the latter. -/
theorem juliaSet_subset_filledJuliaSet {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : JuliaSet f ⊆ FilledJuliaSet f := by
  rw [juliaSet_eq_frontier hd hf]
  exact (isClosed_filledJuliaSet hd hf).frontier_subset

end Work.Normal
