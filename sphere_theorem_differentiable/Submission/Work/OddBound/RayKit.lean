import Submission.GExpRayIdent
import Submission.GExpRayZero
import Submission.RayChart
import Submission.ConjEnergy
import Submission.GExpVelocity
import Submission.GeodesicExtend

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Re-export of the exponential-ray toolkit (for `Submission/Work/OddBound/*` lemmas)

This module imports nothing of its own: it exists so that the lemmas about `GExp`-rays, the
identification of a geodesic with its exponential ray, and the geodesic equation's germ-invariance
can be proved against the main-tree machinery, which cannot be named in a `depends_on` list.

Some of the key items:

* `Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt` — **the ray identification**: a geodesic
  on an open interval containing `0`, based at `p` with velocity `V ≠ 0`, agrees with the `GExp`-ray
  of `V` on `[0,T]`;
* `Submission.GExpRayZero.isGeodesicAt_GExp_smul_all` — `t ↦ GExp p (t • V)` is a geodesic for all
  real `t`;
* `Submission.ConjEnergy.contMDiff_GExp_smul` — the same curve is `C^∞`;
* `Submission.RayChart.curveVelocity_GExp_ne_zero` — its velocity never vanishes;
* `Submission.GExpVelocity.curveVelocity_GExp_smul_zero` — its initial velocity is `V`;
* `Submission.GeodesicExtend.isGeodesicAt_congr_of_eventuallyEq` — the geodesic equation is a germ
  condition.
-/
