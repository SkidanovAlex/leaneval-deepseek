import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.TreeDatum
import Submission.Work.ORBassSerre.Action.Quotient
import Submission.Work.ORBassSerre.Action.QuotientReverse

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre
open Work.ORBassSerre.Action

open Quiver

universe u v

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-! ## The ends of the reversed edge orbit

For an edge orbit `E`, the source orbit of the reversed orbit `orbitEReverse E` is the target
orbit of `E`, and vice versa: reversal just swaps the two ends. -/

/-- The source orbit of the reverse of the orbit of an arrow `u` is the orbit of the target of
`u`. -/
theorem srcE_orbitEReverse_mk (u : Quiver.Total V) :
    Work.ORBassSerre.Action.srcE (G := G) (V := V)
      (Work.ORBassSerre.orbitEReverse (G := G) (V := V) (Quotient.mk'' u)) =
    (Quotient.mk'' u.right : Work.ORBassSerre.orbitV G V) := by
  rw [Work.ORBassSerre.orbitEReverse_mk]
  show Quotient.mk'' (Work.ORBassSerre.Action.orbitRepE (G := G) (V := V)
      (Quotient.mk'' u.reverse)).left = Quotient.mk'' u.right
  rw [← Quiver.Total.reverse_left u]
  exact Work.ORBassSerre.Action.mk_left_eq_of_mk_eq (G := G) (V := V) (w := u.reverse)
    (by rw [Work.ORBassSerre.Action.orbitRepE_mk])

/-- The target orbit of the reverse of the orbit of an arrow `u` is the orbit of the source of
`u`. -/
theorem tgtE_orbitEReverse_mk (u : Quiver.Total V) :
    Work.ORBassSerre.Action.tgtE (G := G) (V := V)
      (Work.ORBassSerre.orbitEReverse (G := G) (V := V) (Quotient.mk'' u)) =
    (Quotient.mk'' u.left : Work.ORBassSerre.orbitV G V) := by
  rw [Work.ORBassSerre.orbitEReverse_mk]
  show Quotient.mk'' (Work.ORBassSerre.Action.orbitRepE (G := G) (V := V)
      (Quotient.mk'' u.reverse)).right = Quotient.mk'' u.left
  rw [← Quiver.Total.reverse_right u]
  exact Work.ORBassSerre.Action.mk_right_eq_of_mk_eq (G := G) (V := V) (w := u.reverse)
    (by rw [Work.ORBassSerre.Action.orbitRepE_mk])

/-- Reversal swaps the source and target orbits. -/
theorem srcE_orbitEReverse (E : Work.ORBassSerre.orbitE G V) :
    Work.ORBassSerre.Action.srcE (G := G) (V := V)
      (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E) =
    Work.ORBassSerre.Action.tgtE (G := G) (V := V) E := by
  rw [show Work.ORBassSerre.orbitEReverse (G := G) (V := V) E =
      Work.ORBassSerre.orbitEReverse (G := G) (V := V)
        (Quotient.mk'' (Work.ORBassSerre.Action.orbitRepE (G := G) (V := V) E)) from by
    rw [Work.ORBassSerre.Action.orbitRepE_mk]]
  rw [show Work.ORBassSerre.Action.srcE (G := G) (V := V)
      (Work.ORBassSerre.orbitEReverse (G := G) (V := V)
        (Quotient.mk'' (Work.ORBassSerre.Action.orbitRepE (G := G) (V := V) E))) =
      (Quotient.mk'' (Work.ORBassSerre.Action.orbitRepE (G := G) (V := V) E).right :
        Work.ORBassSerre.orbitV G V) from
    srcE_orbitEReverse_mk (G := G) (V := V)
      (Work.ORBassSerre.Action.orbitRepE (G := G) (V := V) E)]
  rfl

/-- Reversal swaps the target and source orbits. -/
theorem tgtE_orbitEReverse (E : Work.ORBassSerre.orbitE G V) :
    Work.ORBassSerre.Action.tgtE (G := G) (V := V)
      (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E) =
    Work.ORBassSerre.Action.srcE (G := G) (V := V) E := by
  rw [show Work.ORBassSerre.orbitEReverse (G := G) (V := V) E =
      Work.ORBassSerre.orbitEReverse (G := G) (V := V)
        (Quotient.mk'' (Work.ORBassSerre.Action.orbitRepE (G := G) (V := V) E)) from by
    rw [Work.ORBassSerre.Action.orbitRepE_mk]]
  rw [show Work.ORBassSerre.Action.tgtE (G := G) (V := V)
      (Work.ORBassSerre.orbitEReverse (G := G) (V := V)
        (Quotient.mk'' (Work.ORBassSerre.Action.orbitRepE (G := G) (V := V) E))) =
      (Quotient.mk'' (Work.ORBassSerre.Action.orbitRepE (G := G) (V := V) E).left :
        Work.ORBassSerre.orbitV G V) from
    tgtE_orbitEReverse_mk (G := G) (V := V)
      (Work.ORBassSerre.Action.orbitRepE (G := G) (V := V) E)]
  rfl

/-- **The link of an edge orbit with its reverse.**  The stable letter attached to the reversed
orbit differs from the inverse of the stable letter of the orbit by an element `k` of the vertex
group of the (reversed) source orbit and an element `h` of the vertex group of the (reversed)
target orbit.

Concretely, if `g` carries the lift of `E` to the lift of `orbitEReverse E` (so that
`g • (elift E).reverse = elift (orbitEReverse E)`), then `k = g * sElt E` lies in the stabiliser
of `vert (tgtE E) = vert (srcE (orbitEReverse E))` and `h = g⁻¹ * sElt (orbitEReverse E)` lies in
the stabiliser of `vert (srcE E) = vert (tgtE (orbitEReverse E))`, and
`sElt (orbitEReverse E) = (g * sElt E) * (sElt E)⁻¹ * (g⁻¹ * sElt (orbitEReverse E))`. -/
theorem exists_link {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V) (E : Work.ORBassSerre.orbitE G V) :
    ∃ (k h : G),
      k ∈ d.vgroup (Work.ORBassSerre.Action.srcE (G := G) (V := V)
        (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E)) ∧
      h ∈ d.vgroup (Work.ORBassSerre.Action.tgtE (G := G) (V := V)
        (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E)) ∧
      d.sElt (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E) =
        k * (d.sElt E)⁻¹ * h := by
  obtain ⟨g, hg⟩ := Work.ORBassSerre.Action.exists_smulTotal_of_mk_eq (G := G) (V := V)
    (u := (d.elift E).reverse)
    (w := d.elift (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E))
    (by rw [← Work.ORBassSerre.orbitEReverse_mk, d.elift_orbit E,
      d.elift_orbit (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E)])
  refine ⟨g * d.sElt E, g⁻¹ * d.sElt (Work.ORBassSerre.orbitEReverse (G := G) (V := V) E),
    ?_, ?_, ?_⟩
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

end Work.ORLocInd.FKSKernel.Kurosh
