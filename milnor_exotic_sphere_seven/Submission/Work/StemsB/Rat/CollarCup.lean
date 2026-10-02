import Mathlib
import Submission.Work.StemsB.Rat.CollarDefs
import Submission.Work.StemsB.Rat.CollarSplitFull
import Submission.Work.StemsB.WangDerivation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.StemsB.Rat

noncomputable section

/-- The cup product, in the spelling of `Work.Cohomology.cupH'`. -/
noncomputable def cupT (Y : Type) [TopologicalSpace Y] (m n : ℕ) :=
  Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of Y)) m n

/-- The degree transport, in the spelling of `Work.Cohomology.cupH'`. -/
noncomputable def transT (Y : Type) [TopologicalSpace Y] {k l : ℕ} (h : k = l) :=
  (eqToIso (congrArg (fun t => (Work.Cohomology.SSetCochainComplex ℚ
    (TopCat.toSSet.obj (TopCat.of Y))).homology t) h)).toLinearEquiv.toLinearMap

end

end Work.StemsB.Rat
