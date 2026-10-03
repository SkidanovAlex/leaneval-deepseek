import Submission.Work.ORLocInd.FKSKernel.Kurosh.merge_case3_proof

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Quiver

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre
open Work.ORBassSerre.Action

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]
  {d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V}
  

/-- Case 3 of the merge step of the shortening argument; proved in `merge_case3_proof`. -/
theorem merge_case3 (D : d.PresData) (E : Work.ORBassSerre.orbitE G V) (u v w : G)
    (hu : u ∈ d.vgroup (Work.ORBassSerre.Action.tgtE E))
    (hv : v ∈ d.vgroup (Work.ORBassSerre.Action.srcE E))
    (hw : w ∈ d.vgroup (Work.ORBassSerre.Action.tgtE E))
    (c : ↥(d.eGroup E)) (hc : (d.eGroupToSrc E c : G) = v) :
    d.gEltHom D (Work.ORBassSerre.Action.tgtE E) ⟨u, hu⟩ *
        Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.stepGam D E false *
        d.gEltHom D (Work.ORBassSerre.Action.srcE E) ⟨v, hv⟩ *
        Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.stepGam D E true *
        d.gEltHom D (Work.ORBassSerre.Action.tgtE E) ⟨w, hw⟩ =
      d.gEltHom D (Work.ORBassSerre.Action.tgtE E)
        ⟨u * (d.eGroupToTgt E c : G) * w, mul_mem (mul_mem hu (d.eGroupToTgt E c).2) hw⟩ :=
  merge_case3_proof D E u v w hu hv hw c hc

end Work.ORLocInd.FKSKernel.Kurosh
