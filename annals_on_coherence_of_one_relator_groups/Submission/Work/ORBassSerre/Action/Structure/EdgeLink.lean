import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.TreeDatum
import Submission.Work.ORBassSerre.Action.Structure.exists_link

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Action.Structure

open Quiver

/-!
# The linking element between an edge orbit and its reverse

In the Bass--Serre presentation built in `BSPresentation`, every edge orbit `E` receives its own
stable letter, and the orbit `orbitEReverse E` of the reversed arrows receives a *different*
stable letter.  Staying honest about the geometry requires relating the two: the two chosen lifts
`elift E` and `elift (orbitEReverse E)` differ by a translate, and the two stable letters
`sElt E` and `sElt (orbitEReverse E)` differ by this translate times vertex-group elements.

This file produces the bookkeeping.  For every edge orbit `E` there is a group element `linkG E`
with

* `linkG E • (elift E).reverse = elift (orbitEReverse E)`,
* `linkK E := linkG E * sElt E` lies in the vertex group of `srcE (orbitEReverse E)`,
* `linkH E := (linkG E)⁻¹ * sElt (orbitEReverse E)` lies in the vertex group of
  `tgtE (orbitEReverse E)`,
* `sElt (orbitEReverse E) = linkK E * (sElt E)⁻¹ * linkH E`.

The last identity is a true identity of `G`, so it may be imposed as an additional relation of the
presentation `Gamma`; it is what makes the two codings of a step -- "go along `E` backwards" and
"go along `orbitEReverse E` forwards" -- agree.
-/

universe u v

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

namespace TreeDatum

variable (d : TreeDatum G V)

/-- **The linking element of an edge orbit with its reverse.**  There is a group element `g`
carrying the reverse of the chosen lift of `E` to the chosen lift of the reversed edge orbit, and
for such a `g` the two stable letters differ by vertex group elements. -/
theorem exists_link_lift (E : Work.ORBassSerre.orbitE G V) :
    ∃ g : G,
      g • (d.elift E).reverse = d.elift (Work.ORBassSerre.orbitEReverse E) ∧
      g * d.sElt E ∈
        d.vgroup (srcE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E)) ∧
      g⁻¹ * d.sElt (Work.ORBassSerre.orbitEReverse E) ∈
        d.vgroup (tgtE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E)) ∧
      d.sElt (Work.ORBassSerre.orbitEReverse E) =
        (g * d.sElt E) * (d.sElt E)⁻¹ *
          (g⁻¹ * d.sElt (Work.ORBassSerre.orbitEReverse E)) := by
  obtain ⟨g, hg⟩ := Work.ORBassSerre.Action.exists_smulTotal_of_mk_eq (G := G) (V := V)
    (u := (d.elift E).reverse)
    (w := d.elift (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E))
    (by rw [← Work.ORBassSerre.orbitEReverse_mk, d.elift_orbit E,
      d.elift_orbit (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E)])
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · rw [srcE_orbitEReverse, MulAction.mem_stabilizer_iff]
    have hleft := congrArg Quiver.Total.left hg
    rw [Work.ORBassSerre.Action.smul_left_total, Quiver.Total.reverse_left, d.elift_right,
      ← mul_smul, d.elift_left, srcE_orbitEReverse] at hleft
    exact hleft
  · rw [tgtE_orbitEReverse, MulAction.mem_stabilizer_iff]
    have hright := congrArg Quiver.Total.right hg
    rw [Work.ORBassSerre.Action.smul_right_total, Quiver.Total.reverse_right, d.elift_left,
      d.elift_right, tgtE_orbitEReverse] at hright
    rw [mul_smul, ← hright, ← mul_smul, inv_mul_cancel, one_smul]
  · group

/-- The chosen linking element of an edge orbit with its reversed orbit. -/
noncomputable def linkG (E : Work.ORBassSerre.orbitE G V) : G :=
  Classical.choose (d.exists_link_lift E)

theorem linkG_smul (E : Work.ORBassSerre.orbitE G V) :
    d.linkG E • (d.elift E).reverse = d.elift (Work.ORBassSerre.orbitEReverse E) :=
  (Classical.choose_spec (d.exists_link_lift E)).1

/-- The vertex-group element of the linking identity at the source of the reversed orbit. -/
noncomputable def linkK (E : Work.ORBassSerre.orbitE G V) :
    ↥(d.vgroup (srcE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E))) :=
  ⟨d.linkG E * d.sElt E, (Classical.choose_spec (d.exists_link_lift E)).2.1⟩

/-- The vertex-group element of the linking identity at the target of the reversed orbit. -/
noncomputable def linkH (E : Work.ORBassSerre.orbitE G V) :
    ↥(d.vgroup (tgtE (G := G) (V := V) (Work.ORBassSerre.orbitEReverse E))) :=
  ⟨(d.linkG E)⁻¹ * d.sElt (Work.ORBassSerre.orbitEReverse E),
    (Classical.choose_spec (d.exists_link_lift E)).2.2.1⟩

/-- **The stable letter of the reversed orbit in terms of the stable letter of the orbit.** -/
theorem sElt_orbitEReverse (E : Work.ORBassSerre.orbitE G V) :
    d.sElt (Work.ORBassSerre.orbitEReverse E) =
      (d.linkK E : G) * (d.sElt E)⁻¹ * (d.linkH E : G) :=
  (Classical.choose_spec (d.exists_link_lift E)).2.2.2

end TreeDatum

end Work.ORBassSerre.Action.Structure
