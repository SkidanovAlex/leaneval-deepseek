import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.BSWalk
import Submission.Work.ORBassSerre.Action.Structure.edgeRel_general
import Submission.Work.ORBassSerre.Action.Structure.EdgeLink
import Submission.Work.ORBassSerre.Action.Structure.merge_case1
import Submission.Work.ORBassSerre.Action.Structure.merge_case4

namespace Work.ORBassSerre.Action.Structure

open Quiver

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]
  {d : Work.ORBassSerre.Action.Structure.TreeDatum G V}
  [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)]

/-- **The edge relation in the conjugation form used by the merges.**  The stable letter of an edge
orbit conjugates the target inclusion of the edge group into the source inclusion.  This is the
`false`-direction companion of `stepGam_conj_srcE` (which conjugates the source inclusion into the
target one by the inverse stable letter). -/
theorem stepGam_conj_tgtE (D : d.PresData) (E : Work.ORBassSerre.orbitE G V)
    (c : ↥(d.eGroup E)) :
    TreeDatum.stepGam D E true * d.gEltHom D (Work.ORBassSerre.Action.tgtE E)
        (d.eGroupToTgt E c) * (TreeDatum.stepGam D E true)⁻¹ =
      d.gEltHom D (Work.ORBassSerre.Action.srcE E) (d.eGroupToSrc E c) := by
  have h := stepGam_conj_srcE D E c
  rw [← h]
  group

/-- **Case 2 of the merge step, as a Γ-computation.**  The two half-edges at an edge orbit are
traversed in the same direction, so the two stable letters `stepGam D E true` and
`stepGam D E false = (stepGam D E true)⁻¹` are mutually inverse and the edge relation of the
Bass--Serre presentation conjugates the target vertex-group letter `v = eGroupToTgt E c` into the
source vertex-group letter `eGroupToSrc E c`. -/
theorem merge_case2_proof {G : Type*} {V : Type*}
    [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V]
    {d : Work.ORBassSerre.Action.Structure.TreeDatum G V}
    [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)]
    (D : d.PresData) (E : Work.ORBassSerre.orbitE G V) (u v w : G)
    (hu : u ∈ d.vgroup (Work.ORBassSerre.Action.srcE E))
    (hv : v ∈ d.vgroup (Work.ORBassSerre.Action.tgtE E))
    (hw : w ∈ d.vgroup (Work.ORBassSerre.Action.srcE E))
    (c : ↥(d.eGroup E)) (hc : (d.eGroupToTgt E c : G) = v) :
    d.gEltHom D (Work.ORBassSerre.Action.srcE E) ⟨u, hu⟩ *
        Work.ORBassSerre.Action.Structure.TreeDatum.stepGam D E true *
        d.gEltHom D (Work.ORBassSerre.Action.tgtE E) ⟨v, hv⟩ *
        Work.ORBassSerre.Action.Structure.TreeDatum.stepGam D E false *
        d.gEltHom D (Work.ORBassSerre.Action.srcE E) ⟨w, hw⟩ =
      d.gEltHom D (Work.ORBassSerre.Action.srcE E)
        ⟨u * (d.eGroupToSrc E c : G) * w, mul_mem (mul_mem hu (d.eGroupToSrc E c).2) hw⟩ := by
  classical
  -- the two stable letters are mutually inverse
  have hfalse : TreeDatum.stepGam D E false = (TreeDatum.stepGam D E true)⁻¹ :=
    stepGam_false_eq_inv D E
  -- the hypothesis `hc` identifies the letter `v` with `eGroupToTgt E c`
  have hv' : d.gEltHom D (Work.ORBassSerre.Action.tgtE E) ⟨v, hv⟩ =
      d.gEltHom D (Work.ORBassSerre.Action.tgtE E) (d.eGroupToTgt E c) :=
    congrArg (d.gEltHom D (Work.ORBassSerre.Action.tgtE E)) (Subtype.ext hc.symm)
  rw [hfalse, hv']
  -- expose the conjugated edge-group letter as a single factor
  rw [show d.gEltHom D (srcE E) ⟨u, hu⟩ * TreeDatum.stepGam D E true *
        d.gEltHom D (tgtE E) (d.eGroupToTgt E c) * (TreeDatum.stepGam D E true)⁻¹ *
        d.gEltHom D (srcE E) ⟨w, hw⟩
      = d.gEltHom D (srcE E) ⟨u, hu⟩ *
        (TreeDatum.stepGam D E true * d.gEltHom D (tgtE E) (d.eGroupToTgt E c) *
          (TreeDatum.stepGam D E true)⁻¹) * d.gEltHom D (srcE E) ⟨w, hw⟩ from by group]
  -- apply the edge relation and collect the vertex-group letters at `srcE E`
  rw [stepGam_conj_tgtE D E c, ← map_mul, ← map_mul]
  exact congrArg (d.gEltHom D (srcE E)) (Subtype.ext rfl)

end Work.ORBassSerre.Action.Structure
