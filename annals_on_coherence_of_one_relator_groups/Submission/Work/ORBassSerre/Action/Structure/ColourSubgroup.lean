import Mathlib
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORBassSerre.Action.Cocompact
import Submission.Work.ORBassSerre.Action.fg_of_isCocompact_tree
import Submission.Work.ORBassSerre.Tree.Walk.bipartition_exists
import Submission.Work.ORBassSerre.Tree.Walk.bipartition_eq_of_agree

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Action.Structure

open Quiver

/-!
# The subgroup of elements preserving a bipartition of a tree

A group acting on a tree may contain elements that *reverse* an edge; the Bass--Serre presentation
argument becomes much cleaner for actions without inversions.  The reduction is: fix a 2-colouring
`c : V → Bool` of the tree (`Work.ORBassSerre.Tree.Walk.bipartition_exists`) and let

`colourSubgroup c = {g : G | ∀ w, c (g • w) = c w}`

be the subgroup of elements preserving the colouring.  Every vertex stabiliser and every edge
stabiliser is contained in `colourSubgroup c` (an element fixing a vertex preserves the parity of
the distance from it), so the stabilisers for the `colourSubgroup c`-action are the same as those
for the `G`-action; the subgroup acts without inversions; and it has index at most two (the two
colourings of a connected graph are `c` and its complement).

This file contains the definition and the two elementary facts (stabilisers are contained in it,
and it acts without inversions).
-/

universe u v

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-- The subgroup of elements of `G` preserving a `Bool`-valued colouring `c` of `V`. -/
def colourSubgroup (c : V → Bool) : Subgroup G where
  carrier := {g : G | ∀ w : V, c (g • w) = c w}
  one_mem' := fun w => by rw [one_smul]
  mul_mem' := fun {a b} ha hb w => by
    rw [mul_smul]
    exact (ha (b • w)).trans (hb w)
  inv_mem' := fun {a} ha w => by
    have h := ha (a⁻¹ • w)
    rw [smul_inv_smul] at h
    exact h.symm

@[simp]
theorem mem_colourSubgroup {c : V → Bool} {g : G} :
    g ∈ colourSubgroup (G := G) c ↔ ∀ w : V, c (g • w) = c w := Iff.rfl

/-- The colouring pulled back along `g` is again a colouring. -/
theorem colouring_smul {c : V → Bool} (hc : ∀ e : Quiver.Total V, c e.left ≠ c e.right) (g : G) :
    ∀ e : Quiver.Total V, (fun w => c (g • w)) e.left ≠ (fun w => c (g • w)) e.right := by
  intro e
  show c (g • e.left) ≠ c (g • e.right)
  rw [← Work.ORBassSerre.Action.smul_left_total g e,
    ← Work.ORBassSerre.Action.smul_right_total g e]
  exact hc (g • e)

/-- **A stabiliser is contained in the colour-subgroup.**  An element fixing a vertex sends the
colouring to a colouring agreeing with it at that vertex, hence (by connectivity of a tree) to the
colouring itself. -/
theorem stabilizer_le_colourSubgroup (hT : Work.ORBassSerre.IsTree V) {c : V → Bool}
    (hc : ∀ e : Quiver.Total V, c e.left ≠ c e.right) (v : V) :
    MulAction.stabilizer G v ≤ colourSubgroup (G := G) c := by
  intro g hg
  rw [mem_colourSubgroup]
  have hv : g • v = v := MulAction.mem_stabilizer_iff.mp hg
  have hc' := colouring_smul (G := G) hc g
  have hagree : c v = (fun w => c (g • w)) v := by
    show c v = c (g • v)
    rw [hv]
  have h := Work.ORBassSerre.Tree.Walk.bipartition_eq_of_agree
    (c' := fun w => c (g • w)) hT hc hc' hagree
  intro w
  have hw := congrFun h w
  exact hw.symm

/-- **The colour-subgroup acts without inversions.**  If `g` preserved the colouring and reversed
an edge, the two ends of that edge would have the same colour. -/
theorem actsWithoutInversions_colourSubgroup {c : V → Bool}
    (hc : ∀ e : Quiver.Total V, c e.left ≠ c e.right) :
    Work.ORBassSerre.ActsWithoutInversions ↥(colourSubgroup (G := G) c) V := by
  intro g e hge
  have hg : ∀ w : V, c ((g : G) • w) = c w := g.2
  have h1 : (g : G) • e.left = e.right := by
    have h := congrArg Quiver.Total.left hge
    change (GraphAction.smulTotal (g : G) e).left = e.reverse.left at h
    rw [Work.ORBassSerre.GraphAction.smul_left (g : G) e, Quiver.Total.reverse_left] at h
    exact h
  exact hc e ((hg e.left).symm.trans (congrArg c h1))

end Work.ORBassSerre.Action.Structure
