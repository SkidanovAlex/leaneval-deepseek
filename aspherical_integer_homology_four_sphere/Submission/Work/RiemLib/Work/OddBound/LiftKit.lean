import Submission.Work.RiemLib.RauchK
import Submission.Work.RiemLib.Geodesic
import Submission.Work.RiemLib.GeodesicSpeed
import Submission.Work.RiemLib.Length
import Submission.Work.RiemLib.Distance
import Submission.Work.RiemLib.InjRadius
import Submission.Work.RiemLib.InjBall
import Submission.Work.RiemLib.SegmentDomain
import Submission.Work.RiemLib.LiftLemma
import Submission.Work.RiemLib.LiftUniform
import Submission.Work.RiemLib.LiftGlobal
import Submission.Work.RiemLib.GeoLimit
import Submission.Work.RiemLib.GExpLocalInj
import Submission.Work.RiemLib.LocalInj
import Submission.Work.RiemLib.XuLift
import Submission.Work.RiemLib.XuMain
import Submission.Work.RiemLib.CurveCover
import Submission.Work.RiemLib.InjHalf
import Submission.Work.RiemLib.LensLoop
import Submission.Work.RiemLib.UniformInj
import Submission.Work.RiemLib.ConjRadius
import Submission.Work.RiemLib.ConjCut
import Submission.Work.RiemLib.SingularConj
import Submission.Work.RiemLib.RayConj
import Submission.Work.RiemLib.Gauss
import Submission.Work.RiemLib.ExpBound2
import Submission.Work.RiemLib.JacobiGlobal
import Submission.Work.RiemLib.JacobiGauss
import Submission.Work.RiemLib.GExpFlow
import Submission.Work.RiemLib.Minimal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Re-export of the lifting / normal-ball toolkit (for `Submission/Work/OddBound/*` lemmas)

Used by the long homotopy lemma (`Work.OddBound.long_homotopy_lemma`), whose proof lifts the two
halves of the closed curves of a null-homotopy under the exponential map at their base point.  The
relevant machinery lives in the main tree (`InjBall`, `SegmentDomain`, `LiftLemma`, `LiftUniform`,
`LiftGlobal`, `GeoLimit`, `GExpLocalInj`, `CurveCover`, `InjHalf`, `LensLoop`, `XuMain`,
`ConjCut`, `Gauss`, `ExpBound2`, `JacobiGlobal`, `JacobiGauss`, `GExpFlow`), which cannot be
named in a `depends_on` list.

Some of the key items:

* `Submission.XuMain.exists_pos_ball_lift_GExp_forall_le` — the **inverse function theorem** for
  `GExp p` at a vector with invertible differential, *with a prescribed radius*;
* `Submission.XuLift.isLocalDiffeomorphAt_GExp` — `GExp p` is a **local diffeomorphism** at such a
  vector;
* `Submission.ConjCut.isInvertible_mfderiv_GExp_of_norm_lt_pi_div_sqrt` — the differential of
  `GExp p` is invertible at every non-zero vector of norm `< π/√K` when `sec ≤ K`, `0 < K`;
* `Submission.ConjCut.not_isConjugateTime_of_lt_pi_div_sqrt` — no conjugate time below `π/√K`;
* `Submission.Gauss.gauss_lemma_fderiv` and `Submission.ExpBound2.mfderiv_expMap_norm_le` — Gauss's
  lemma and Rauch's contraction bound for the differential of the exponential map (in the chart
  model of a base point);
* `Submission.JacobiGauss.jacobi_velocity` — the radial Jacobi field is `t` times the velocity;
* `Submission.LiftLemma.exists_continuous_lift` — the continuous *minimising* lift of a curve under
  `GExp p`, available below the injectivity radius.
-/
