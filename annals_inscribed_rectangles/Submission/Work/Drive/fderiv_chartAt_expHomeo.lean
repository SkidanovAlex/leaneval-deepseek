import Mathlib
import Submission.Work.Drive.eventuallyEq_chartAt_expHomeo
import Submission.Work.Drive.logEuclEquiv

/-!
# The derivative of the chart of `(0,∞)`, in terms of `log`

Composing `Work.Drive.eventuallyEq_chartAt_expHomeo` with the derivative of a composite with a
continuous linear map: the chart of the pushed-forward structure of `(0,∞)` has, along a curve `r`, the
derivative `logEucl.comp (fderiv (log ∘ r) z)`.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold Topology Filter

/-- **The derivative of the pushed chart of `(0,∞)`.** -/
theorem fderiv_chartAt_expHomeo
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (r : Z → Set.Ioi (0 : ℝ)) (z : Z) (q' : Set.Ioi (0 : ℝ))
    (hrc : ContinuousAt r z)
    (hz : r z ∈ (@chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0 : ℝ)) _
        (Homeomorph.chartedSpace Work.Drive.expHomeo) q').source)
    (hrd : DifferentiableAt ℝ (fun u => Real.log (r u)) z) :
    fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0 : ℝ)) _
        (Homeomorph.chartedSpace Work.Drive.expHomeo) q' (r u)) z
      = Work.Drive.logEucl.comp (fderiv ℝ (fun u => Real.log (r u)) z) := by
  rw [(Work.Drive.eventuallyEq_chartAt_expHomeo r z q' hrc hz).fderiv_eq]
  exact (Work.Drive.logEucl.hasFDerivAt.comp z hrd.hasFDerivAt).fderiv

end Work.Drive
