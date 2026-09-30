import Submission.Work.Curvature.Main
import Submission.Work.Profiles.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Interface to the filling profiles of `Work.Profiles`

`Work.Profiles.FillProfile` provides the warping functions `f, h` of the filling region
(`ContDiff ℝ ∞`, `f > 0` on `r > 0`, `h > 0`, `f' ≥ 0`, `h' ≥ 0`, `f'' ≥ 0`, `h'' ≥ 0`), i.e.
exactly the hypotheses of `Work.Curvature.warped_sec_nonpos` at `r = q 0` inside the filling
region `{q 0 > 0}`.  This file records that the profiles of `Work.Profiles` therefore satisfy
`SecNonposAt (warpedMetric P.f P.h) q` at every `q` of the filling region.

This file is deliberately *not* imported by `Work.Curvature.Main`, so that the curvature chapter
itself does not depend on the profile chapter.
-/

open scoped ContDiff
open Filter Topology

namespace Work.Curvature

noncomputable section

/-- **The filling profiles have non-positive warped sectional curvature.** -/
theorem secNonposAt_fillProfile (P : Work.Profiles.FillProfile) (q : E4) (hq : 0 < q 0) :
    SecNonposAt (warpedMetric P.f P.h) q := by
  have h2infty : (2 : WithTop ℕ∞) ≤ ∞ := by norm_num
  exact secNonposAt_warped P.f P.h q (P.f_smooth.of_le h2infty) (P.h_smooth.of_le h2infty)
    (P.f_pos (q 0) hq) (P.h_pos (q 0)) (P.f_mono (q 0)) (P.h_mono (q 0))
    (P.f_convex (q 0)) (P.h_convex (q 0))

end

end Work.Curvature
