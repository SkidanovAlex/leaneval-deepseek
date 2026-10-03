import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.BSWalk
import Submission.Work.ORBassSerre.Action.Structure.edgeRel_general
import Submission.Work.ORBassSerre.Action.Structure.EdgeLink
import Submission.Work.ORBassSerre.Action.Structure.merge_case1
import Submission.Work.ORBassSerre.Action.Structure.merge_case4

namespace Work.ORBassSerre.Action.Structure

open Quiver

theorem merge_case3_proof {G : Type*} {V : Type*}
    [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V]
    {d : Work.ORBassSerre.Action.Structure.TreeDatum G V}
    [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)]
    (D : d.PresData) (E : Work.ORBassSerre.orbitE G V) (u v w : G)
    (hu : u ∈ d.vgroup (Work.ORBassSerre.Action.tgtE E))
    (hv : v ∈ d.vgroup (Work.ORBassSerre.Action.srcE E))
    (hw : w ∈ d.vgroup (Work.ORBassSerre.Action.tgtE E))
    (c : ↥(d.eGroup E)) (hc : (d.eGroupToSrc E c : G) = v) :
    d.gEltHom D (Work.ORBassSerre.Action.tgtE E) ⟨u, hu⟩ *
        Work.ORBassSerre.Action.Structure.TreeDatum.stepGam D E false *
        d.gEltHom D (Work.ORBassSerre.Action.srcE E) ⟨v, hv⟩ *
        Work.ORBassSerre.Action.Structure.TreeDatum.stepGam D E true *
        d.gEltHom D (Work.ORBassSerre.Action.tgtE E) ⟨w, hw⟩ =
      d.gEltHom D (Work.ORBassSerre.Action.tgtE E)
        ⟨u * (d.eGroupToTgt E c : G) * w, mul_mem (mul_mem hu (d.eGroupToTgt E c).2) hw⟩ := by
  classical
  -- Replace the middle vertex-group letter `⟨v, hv⟩` by the edge-group inclusion `eGroupToSrc E c`.
  have hv' : d.gEltHom D (Work.ORBassSerre.Action.srcE E) ⟨v, hv⟩ =
      d.gEltHom D (Work.ORBassSerre.Action.srcE E) (d.eGroupToSrc E c) :=
    congrArg _ (Subtype.ext hc.symm)
  -- The backwards stable letter is the inverse of the forwards one.
  rw [stepGam_false_eq_inv D (E := E), hv']
  -- Isolate the conjugating block `t⁻¹ * ĝ(c) * t`.
  rw [show d.gEltHom D (Work.ORBassSerre.Action.tgtE E) ⟨u, hu⟩ *
        (TreeDatum.stepGam D E true)⁻¹ *
        d.gEltHom D (Work.ORBassSerre.Action.srcE E) (d.eGroupToSrc E c) *
        TreeDatum.stepGam D E true *
        d.gEltHom D (Work.ORBassSerre.Action.tgtE E) ⟨w, hw⟩ =
      d.gEltHom D (Work.ORBassSerre.Action.tgtE E) ⟨u, hu⟩ *
        ((TreeDatum.stepGam D E true)⁻¹ *
          d.gEltHom D (Work.ORBassSerre.Action.srcE E) (d.eGroupToSrc E c) *
          TreeDatum.stepGam D E true) *
        d.gEltHom D (Work.ORBassSerre.Action.tgtE E) ⟨w, hw⟩ from by group,
    stepGam_conj_srcE D E c]
  -- Collect the three remaining vertex-group letters at the common orbit `tgtE E`.
  simp only [← map_mul]
  refine congrArg (d.gEltHom D (Work.ORBassSerre.Action.tgtE E)) (Subtype.ext ?_)
  simp

end Work.ORBassSerre.Action.Structure
