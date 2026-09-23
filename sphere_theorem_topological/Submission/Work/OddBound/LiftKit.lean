import Submission.RauchK
import Submission.Geodesic
import Submission.GeodesicSpeed
import Submission.Length
import Submission.Distance
import Submission.InjRadius
import Submission.InjBall
import Submission.SegmentDomain
import Submission.LiftLemma
import Submission.LiftUniform
import Submission.LiftGlobal
import Submission.GeoLimit
import Submission.GExpLocalInj
import Submission.LocalInj
import Submission.XuLift
import Submission.XuMain
import Submission.CurveCover
import Submission.InjHalf
import Submission.LensLoop
import Submission.UniformInj
import Submission.ConjRadius
import Submission.ConjCut
import Submission.SingularConj
import Submission.RayConj
import Submission.Gauss
import Submission.ExpBound2
import Submission.JacobiGlobal
import Submission.JacobiGauss
import Submission.GExpFlow
import Submission.Minimal

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
