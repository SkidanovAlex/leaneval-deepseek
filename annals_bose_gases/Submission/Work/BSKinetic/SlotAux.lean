import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BSKinetic.SlotAux` — the measure of the remaining box

The slot decomposition of the `(n+1)`-body words of `Submission.Work.BSKinetic.Defs` is read
against the restricted measure `volume.restrict (abox n ℓ)` on the remaining particles.  This
module names it, so that statements about it can be written without opening `MeasureTheory`.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BSKinetic

set_option autoImplicit false

/-- The restricted volume on the remaining box: the measure against which the slot sums over
`r : X n` are integrated. -/
noncomputable def boxMu (n : ℕ) (ℓ : ℝ) : Measure (Submission.BoseGases.X n) :=
  (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)

end Work.BSKinetic
