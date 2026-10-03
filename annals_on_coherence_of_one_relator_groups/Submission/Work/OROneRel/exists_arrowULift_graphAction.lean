import Mathlib
import Submission.Work.OROneRel.arrowULift
import Submission.Work.ORBassSerre.Interface

/-!
# Transport of a graph action along the arrow-`ULift` of a quiver

`Work.OROneRel.arrowULift` builds, on the *same* vertex type `V`, the quiver `arrowULiftQuiver V Q`
whose arrows are the `ULift` of the arrows of `Q` (so that one can move the quiver to a larger
universe of arrows), together with the transported (involutive) reversal.

Here we transport a *group action on the graph*: from an action `A` of a group `G` on the graph
`(V, Q)` we build an action `A'` of `G` on the arrow-lifted graph `(V, arrowULiftQuiver V Q)`,
and we show that `A'` is without inversions as soon as `A` is.  The whole construction goes through
the two inverse bijections

* `totalArrowULiftDown : Quiver.Total (arrowULiftQuiver V Q) → Quiver.Total V`,
* `totalArrowULiftUp : Quiver.Total V → Quiver.Total (arrowULiftQuiver V Q)`

on the types of *all arrows*; both commute with sources, targets and reversal (the latter two facts
are `totalArrowULiftDown_reverse` and `totalArrowULiftUp_reverse`).

This is the last graph-theoretic input needed to make a `G`-tree out of a tree whose quiver of
arrows lives in an inconvenient universe.

## Main results

* `Work.OROneRel.arrowULiftGraphAction` : the transported graph action
* `Work.OROneRel.actsWithoutInversions_arrowULift` : transport of "no inversions"
* `Work.OROneRel.exists_arrowULift_graphAction` : the two together, in the form requested by the
  caller
-/

set_option autoImplicit false
set_option warn.classDefReducibility false

universe u v w

namespace Work.OROneRel

open Quiver

/-! ## The two bijections on all arrows -/

/-- An arrow of the arrow-lifted quiver, as an arrow of the original quiver, together with
source and target. -/
def totalArrowULiftDown {V : Type u} {Q : Quiver.{v, u} V} :
    @Quiver.Total V (arrowULiftQuiver.{u, v, w} V Q) → @Quiver.Total V Q :=
  fun e => @Quiver.Total.mk V Q
    (@Quiver.Total.left V (arrowULiftQuiver.{u, v, w} V Q) e)
    (@Quiver.Total.right V (arrowULiftQuiver.{u, v, w} V Q) e)
    ((@Quiver.Total.hom V (arrowULiftQuiver.{u, v, w} V Q) e).down)

/-- An arrow of the original quiver, as an arrow of the arrow-lifted quiver. -/
def totalArrowULiftUp {V : Type u} {Q : Quiver.{v, u} V} :
    @Quiver.Total V Q → @Quiver.Total V (arrowULiftQuiver.{u, v, w} V Q) :=
  fun e => @Quiver.Total.mk V (arrowULiftQuiver.{u, v, w} V Q)
    (@Quiver.Total.left V Q e)
    (@Quiver.Total.right V Q e)
    (ULift.up (@Quiver.Total.hom V Q e))

@[simp] theorem totalArrowULiftDown_up {V : Type u} {Q : Quiver.{v, u} V}
    (e : @Quiver.Total V Q) : totalArrowULiftDown (totalArrowULiftUp e) = e := by
  simp only [totalArrowULiftDown, totalArrowULiftUp]

@[simp] theorem totalArrowULiftUp_down {V : Type u} {Q : Quiver.{v, u} V}
    (e : @Quiver.Total V (arrowULiftQuiver.{u, v, w} V Q)) :
    totalArrowULiftUp (totalArrowULiftDown e) = e := by
  simp only [totalArrowULiftDown, totalArrowULiftUp]
  rfl

/-- The "down" bijection commutes with reversal. -/
theorem totalArrowULiftDown_reverse {V : Type u} {Q : Quiver.{v, u} V} [HR : Quiver.HasReverse V]
    (e : @Quiver.Total V (arrowULiftQuiver.{u, v, w} V Q)) :
    totalArrowULiftDown (@Quiver.Total.reverse V (arrowULiftQuiver.{u, v, w} V Q)
        (arrowULiftHasReverse.{u, v, w} V Q HR) e)
      = @Quiver.Total.reverse V Q HR (totalArrowULiftDown e) := by
  simp only [totalArrowULiftDown, Quiver.Total.reverse]
  rfl

/-- The "up" bijection commutes with reversal. -/
theorem totalArrowULiftUp_reverse {V : Type u} {Q : Quiver.{v, u} V} [HR : Quiver.HasReverse V]
    (e : @Quiver.Total V Q) :
    totalArrowULiftUp (@Quiver.Total.reverse V Q HR e)
      = @Quiver.Total.reverse V (arrowULiftQuiver.{u, v, w} V Q)
          (arrowULiftHasReverse.{u, v, w} V Q HR) (totalArrowULiftUp e) := by
  simp only [totalArrowULiftUp, Quiver.Total.reverse]
  rfl

/-! ## The transported graph action -/

/-- The action of `G` on the arrows of the arrow-lifted graph: conjugate the original action on
arrows by the two bijections above. -/
def arrowULiftSmulTotal {G : Type u} {V : Type u} [Group G] {Q : Quiver.{v, u} V}
    [M : MulAction G V] [HR : Quiver.HasReverse V]
    [GA : @Work.ORBassSerre.GraphAction G V _ Q HR M]
    (g : G) (e : @Quiver.Total V (arrowULiftQuiver.{u, v, w} V Q)) :
    @Quiver.Total V (arrowULiftQuiver.{u, v, w} V Q) :=
  totalArrowULiftUp
    (@Work.ORBassSerre.GraphAction.smulTotal G V _ Q HR M GA g (totalArrowULiftDown e))

/-- **A graph action transports along the arrow-`ULift`.**  From a `G`-action on the graph
`(V, Q)` we build a `G`-action on `(V, arrowULiftQuiver V Q)`. -/
def arrowULiftGraphAction {G : Type u} {V : Type u} [Group G] {Q : Quiver.{v, u} V}
    [M : MulAction G V] [HR : Quiver.HasReverse V]
    [GA : @Work.ORBassSerre.GraphAction G V _ Q HR M] :
    @Work.ORBassSerre.GraphAction G V _ (arrowULiftQuiver.{u, v, w} V Q)
      (arrowULiftHasReverse.{u, v, w} V Q HR) M := by
  refine @Work.ORBassSerre.GraphAction.mk G V _ (arrowULiftQuiver.{u, v, w} V Q)
    (arrowULiftHasReverse.{u, v, w} V Q HR) M arrowULiftSmulTotal ?_ ?_ ?_ ?_ ?_
  · intro e
    simp only [arrowULiftSmulTotal, Work.ORBassSerre.GraphAction.smulTotal_one,
      totalArrowULiftUp_down]
  · intro g h e
    simp only [arrowULiftSmulTotal, totalArrowULiftDown_up,
      Work.ORBassSerre.GraphAction.smulTotal_mul]
  · intro g e
    simp only [arrowULiftSmulTotal, totalArrowULiftDown, totalArrowULiftUp,
      Work.ORBassSerre.GraphAction.smul_left]
  · intro g e
    simp only [arrowULiftSmulTotal, totalArrowULiftDown, totalArrowULiftUp,
      Work.ORBassSerre.GraphAction.smul_right]
  · intro g e
    simp only [arrowULiftSmulTotal, totalArrowULiftDown_reverse,
      Work.ORBassSerre.GraphAction.smul_reverse, totalArrowULiftUp_reverse]

/-- **"No inversions" transports along the arrow-`ULift`:** the transported action reverses no
arrow whenever the original one does not. -/
theorem actsWithoutInversions_arrowULift {G : Type u} {V : Type u} [Group G] {Q : Quiver.{v, u} V}
    [M : MulAction G V] [HR : Quiver.HasReverse V]
    [GA : @Work.ORBassSerre.GraphAction G V _ Q HR M]
    (h : @Work.ORBassSerre.ActsWithoutInversions G V _ Q HR M GA) :
    @Work.ORBassSerre.ActsWithoutInversions G V _ (arrowULiftQuiver.{u, v, w} V Q)
      (arrowULiftHasReverse.{u, v, w} V Q HR) M
      (arrowULiftGraphAction (Q := Q) (M := M) (HR := HR) (GA := GA)) := by
  intro g e heq
  refine h g (totalArrowULiftDown e) ?_
  have hc := congrArg totalArrowULiftDown heq
  simp only [totalArrowULiftDown_reverse] at hc
  exact hc

theorem exists_arrowULift_graphAction {G : Type u} [Group G] {V : Type u} {Q : Quiver.{v, u} V} (R : @Quiver.HasInvolutiveReverse V Q) (M : MulAction G V) (A : @Work.ORBassSerre.GraphAction G V _ Q R.toHasReverse M) : ∃ A' : @Work.ORBassSerre.GraphAction G V _ (Work.OROneRel.arrowULiftQuiver V Q) (Work.OROneRel.arrowULiftHasInvolutiveReverse V Q R).toHasReverse M, (@Work.ORBassSerre.ActsWithoutInversions G V _ Q R.toHasReverse M A → @Work.ORBassSerre.ActsWithoutInversions G V _ (Work.OROneRel.arrowULiftQuiver V Q) (Work.OROneRel.arrowULiftHasInvolutiveReverse V Q R).toHasReverse M A') := by
  refine ⟨arrowULiftGraphAction (Q := Q) (M := M) (HR := R.toHasReverse) (GA := A), ?_⟩
  intro h
  exact actsWithoutInversions_arrowULift (Q := Q) (M := M) (HR := R.toHasReverse) (GA := A) h

end Work.OROneRel
