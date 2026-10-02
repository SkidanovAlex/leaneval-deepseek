import Mathlib
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Escape

/-- The Green function is a limit of the nonnegative partial Green functions, hence nonnegative.

There is no escaping a point where the partial Green functions are already nonnegative: the
partial sums `greenIter f d z n = d^{-n} log⁺ ‖f^[n] z‖` are `≥ 0` by definition of `log⁺`, and
`green f d z` is their limit along `atTop` (`tendsto_greenIter`), so `closedness` of `[0, ∞)`
gives `0 ≤ green f d z`. -/
theorem green_nonneg (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d) (z : ℂ) :
    0 ≤ green f d z :=
  ge_of_tendsto (tendsto_greenIter f d A h hd z)
    (Filter.Eventually.of_forall fun n => greenIter_nonneg f d z n)

end Work.Escape
