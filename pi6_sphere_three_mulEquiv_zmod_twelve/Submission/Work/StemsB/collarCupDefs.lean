import Mathlib
import Submission.Work.StemsB.collarSigmaDefs
import Submission.Work.StemsB.collarSplitFull
import Submission.Work.StemsB.WangDerivation

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

/-- The cup product, in the spelling of `Work.Cohomology.cupH'`. -/
noncomputable def cupT (Y : Type) [TopologicalSpace Y] (m n : ℕ) :=
  Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of Y)) m n

/-- The degree transport, in the spelling of `Work.Cohomology.cupH'`. -/
noncomputable def transT (Y : Type) [TopologicalSpace Y] {k l : ℕ} (h : k = l) :=
  (eqToIso (congrArg (fun t => (Work.Cohomology.SSetCochainComplex ℤ
    (TopCat.toSSet.obj (TopCat.of Y))).homology t) h)).toLinearEquiv.toLinearMap

end

end Work.StemsB
