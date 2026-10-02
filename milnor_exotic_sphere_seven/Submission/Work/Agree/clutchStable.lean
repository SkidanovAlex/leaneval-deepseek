import Mathlib
import Submission.Work.Agree.S4Bundle
import Submission.Work.Gen.EulerToolkit
import Submission.Work.Agree.sphereStableTrivial
import Submission.Work.Whitney.Basic
import Submission.Work.Agree.clutchAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Agree

theorem clutchStable (ι₀ ι' : Type) [Inhabited ι₀] [Inhabited ι'] :
    Nonempty (Work.Thom.BundleIso
      (Work.TangentClasses.RealBundle.sum (Work.Agree.clutchBundle (1 : ℤ) 1)
        (Work.TangentClasses.RealBundle.trivial Work.Agree.S4 (EuclideanSpace ℝ (Fin 1)) ι₀))
      (Work.TangentClasses.RealBundle.trivial Work.Agree.S4 (EuclideanSpace ℝ (Fin 5)) ι')) :=
  clutchStable_aux ι₀ ι'

end Work.Agree
