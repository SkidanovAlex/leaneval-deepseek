/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/DiaDefs.lean`

The measure used by the diagonal-energy lemmas of `EpsE4Thr`: `dz dθ` on the quadrant
`Iz × Iθ` (`Work.Spaces.Iz = [0,∞)`, `Work.Spaces.Iθ = [0,π/2]`), as the product of the two
restricted Lebesgue measures.  It is an `abbrev` so that it is definitionally equal to the
explicit product measure appearing in the statements of the consumers.
-/

import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

noncomputable section

namespace Work.FTS.StrongEps.EpsE4Thr

/-- The measure `dz dθ` on the quadrant `Iz × Iθ`. -/
abbrev diaM : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

end Work.FTS.StrongEps.EpsE4Thr
