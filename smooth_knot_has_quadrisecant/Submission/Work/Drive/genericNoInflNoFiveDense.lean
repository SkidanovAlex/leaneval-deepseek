import Mathlib
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.Work.Drive.genericNoInflNoFiveDenseProved

/-!
# Step 1' of the generic reduction: the five-collinear-free generic density

`Work.Drive.genericNoInflNoFiveDense`: every smooth knot has arbitrarily `C¹`-close smooth
approximants which are simultaneously in transverse general position, without inflection points and
without five collinear points.

This is the density input `hA` of the assembly
`Work.Drive.quadrisecant_of_genericCase_noInfl_of_ingredients`.  Its proof is
`Work.Drive.genericNoInflNoFiveDense_proved`
(`Submission/Work/Drive/genericNoInflNoFiveDenseProved.lean`), which combines the two proved halves:
the bad-set lemma `Work.Drive.noFiveCollinear_bad_interior_empty` (rank `6 > 5`) and the Baire
assembly `Work.Drive.genericNoInflNoFiveDense_of_bad5`.  The present module only re-exports it
under the name used by the reduction.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-- **Step 1' (density with no five collinear points).**  Every smooth knot has arbitrarily
`C¹`-close approximants in transverse general position, without inflections and without five
collinear points. -/
theorem genericNoInflNoFiveDense : GenericNoInflNoFiveDense :=
  genericNoInflNoFiveDense_proved

end

end Work.Drive
