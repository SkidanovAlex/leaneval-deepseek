import Mathlib
import Submission.Work.Drive.contMDiffAt_cappingSpace_configPiece
import Submission.Work.Drive.chartAt_homeomorph_chartedSpace

/-!
# The chart of the pushed-forward structure of `(0,∞)` is `log`

`Work.Drive.expHomeo : ℝ¹ ≃ₜ (0,∞)` transports the self-chart of `ℝ¹` to `(0,∞)`.  This file records
what that chart is: along any curve `r` with values in `(0,∞)`,

> `chartAt q (r u) = logEucl (Real.log (r u))`  for `u` near the base point,

with `Work.Drive.logEucl : ℝ →L ℝ¹` the linear identification of `ℝ` with `ℝ¹`
(`Work.Drive.expHomeo_symm_apply`).  This is the identification that turns the first component of the
chart of `Work.Drive.halfLineProjectiveCharted` into the *level block* of the radial sweep
(`Work.Drive.fderiv_log_levelOf_clampedSweep_eq`).
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold Topology Filter

/-- **The chart of `(0,∞)` pushed forward along `expHomeo` is `logEucl ∘ log`.** -/
theorem eventuallyEq_chartAt_expHomeo
    {Z : Type*} [TopologicalSpace Z]
    (r : Z → Set.Ioi (0 : ℝ)) (z : Z) (q : Set.Ioi (0 : ℝ))
    (hr : ContinuousAt r z)
    (hz : r z ∈ (@chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0 : ℝ)) _
        (Homeomorph.chartedSpace Work.Drive.expHomeo) q).source) :
    Filter.EventuallyEq (nhds z)
      (fun u => @chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0 : ℝ)) _
        (Homeomorph.chartedSpace Work.Drive.expHomeo) q (r u))
      (fun u => Work.Drive.logEucl (Real.log (r u))) := by
  have h := Work.Drive.eventuallyEq_chartAt_homeomorph_chartedSpace
    (H := EuclideanSpace ℝ (Fin 1)) (M := EuclideanSpace ℝ (Fin 1))
    (M' := Set.Ioi (0 : ℝ)) Work.Drive.expHomeo r z q hr hz
  have h2 : (fun u : Z => chartAt (EuclideanSpace ℝ (Fin 1))
        (Work.Drive.expHomeo.symm q) (Work.Drive.expHomeo.symm (r u)))
      = fun u : Z => Work.Drive.logEucl (Real.log (r u)) := by
    funext u
    rw [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, Work.Drive.expHomeo_symm_apply]
    rfl
  exact h.trans (Filter.EventuallyEq.of_eq h2)

end Work.Drive
