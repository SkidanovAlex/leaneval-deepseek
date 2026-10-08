import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.CORE2A.thm26_aux
import Submission.OddOrder.GroupTheory.FittingSelfCentralizing

namespace Work.DSTR

/-- **E1 / Bender 1.2** in this area's vocabulary: for a finite solvable group the Fitting subgroup contains its centralizer.  This is `OddOrder.GroupTheory.centralizer_fitting_le_fitting` of the FT closure, transported from `OddOrder.Isaacs.Ch01.fitting` to `Work.GW2.fitting`. -/
theorem fittingSelfCentralizing : Work.GW2.FittingSelfCentralizingProp := by
  intro X _ _ hsol
  have hfit : Work.GW2.fitting X = OddOrder.Isaacs.Ch01.fitting X :=
    Work.CORE2A.fitting_eq_isaacsFitting
  rw [hfit]
  exact @OddOrder.GroupTheory.centralizer_fitting_le_fitting X _ _ hsol

end Work.DSTR
