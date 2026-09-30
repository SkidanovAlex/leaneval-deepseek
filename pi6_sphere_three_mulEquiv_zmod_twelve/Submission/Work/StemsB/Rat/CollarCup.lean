import Mathlib
import Submission.Work.StemsB.Rat.CollarDefs
import Submission.Work.StemsB.Rat.CollarSplitFull
import Submission.Work.StemsB.WangDerivation

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
