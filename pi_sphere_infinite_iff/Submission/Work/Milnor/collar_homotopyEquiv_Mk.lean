import Mathlib
import Submission.Work.Milnor.Collar
import Submission.Work.Milnor.VBundle
import Submission.Work.Milnor.mk_to_vk
import Submission.Work.Milnor.fibreNorm
import Submission.Work.Milnor.ScaleDefs
import Submission.Work.Milnor.UnitSphere
import Submission.Work.Milnor.CollarHomotopy

namespace Work.Milnor

/-- **The collar `{1/2 < ν}` of the disc bundle of `ξ` is homotopy equivalent to the sphere bundle
`Mk k`.**  The homotopy equivalence is the normalisation `p ↦ (ν p)⁻¹ • p` in one direction and
the inclusion of the unit sphere bundle `Mk k → Vk k` in the other; see
`Submission.Work.Milnor.CollarHomotopy`. -/
theorem collar_homotopyEquiv_Mk (k : ℤ) :
    Nonempty (ContinuousMap.HomotopyEquiv (↥(Work.Milnor.collar k)) (Submission.Milnor.Mk k)) :=
  collar_homotopyEquiv_aux k

end Work.Milnor
