import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELTop.isOpen_polyRegion
import Submission.Work.ELTop.isClosed_polyCurve

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELNest

theorem isOpen_D {c : ℂ} (S : Work.ELNest.NestData c) (n : ℕ) : IsOpen (S.D n) := by
  rw [NestData.D]
  exact Work.ELTop.isOpen_polyRegion S.d.hN [S.Za n, S.Zb n, S.Zc n] (Dlev S.L n)
    (Work.ELTop.isClosed_polyCurve S.d.hN [S.Za n, S.Zb n, S.Zc n] (Dlev S.L n))

end Work.ELNest
