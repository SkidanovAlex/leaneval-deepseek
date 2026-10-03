import Mathlib
import Submission.Work.ORBassSerre.Interface

/-!
# Arrow-`ULift` transport of a graph (definitions)

The conclusion of `Work.OROneRel.winRhoRange_tree` is *universe-polymorphic in the universe of the
arrows of the quiver* (see `#check @winRhoRange_tree`, which reports `Quiver.{u_1, 0} V`), while
the coset graph `GradedHNN.Coset H t` carries its arrows at universe `0`.  To satisfy the target we
therefore need the **arrow-lifted** quiver on the *same* vertex type: same vertices, arrows the
`ULift` of the arrows of the original quiver.

This file provides only the definitions (defs on arrows and paths); the transport of the
graph-theoretic invariants (`IsTree`, `ActsWithoutInversions`, the graph action) is proved in
`Submission/Work/OROneRel/arrowULiftIsTree.lean` and companions.
-/

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace Work.OROneRel

open Quiver

/-- **The arrow-lifted quiver**: the same vertices as `V`, with the arrows of `Q` lifted to the
universe `max v w`. -/
def arrowULiftQuiver.{u, v, w} (V : Type u) (Q : Quiver.{v, u} V) : Quiver.{max v w, u} V :=
  ⟨fun a b => ULift.{w, v} (Q.Hom a b)⟩

/-- The arrow-lifted quiver has the `ULift`ed arrows of the original one. -/
theorem arrowULiftQuiver_hom.{u, v, w} (V : Type u) (Q : Quiver.{v, u} V) (a b : V) :
    (arrowULiftQuiver.{u, v, w} V Q).Hom a b = ULift.{w, v} (Q.Hom a b) := rfl

/-- An arrow of the original quiver, as an arrow of the arrow-lifted quiver. -/
def arrowULiftUp.{u, v, w} {V : Type u} {Q : Quiver.{v, u} V} {a b : V} (f : Q.Hom a b) :
    (arrowULiftQuiver.{u, v, w} V Q).Hom a b := ⟨f⟩

/-- An arrow of the arrow-lifted quiver, as an arrow of the original quiver. -/
def arrowULiftDown.{u, v, w} {V : Type u} {Q : Quiver.{v, u} V} {a b : V}
    (f : (arrowULiftQuiver.{u, v, w} V Q).Hom a b) : Q.Hom a b := f.down

@[simp] theorem arrowULiftUp_down.{u, v, w} {V : Type u} {Q : Quiver.{v, u} V} {a b : V}
    (f : Q.Hom a b) : arrowULiftDown.{u, v, w} (arrowULiftUp.{u, v, w} f) = f := rfl

@[simp] theorem arrowULiftDown_up.{u, v, w} {V : Type u} {Q : Quiver.{v, u} V} {a b : V}
    (f : (arrowULiftQuiver.{u, v, w} V Q).Hom a b) :
    arrowULiftUp.{u, v, w} (arrowULiftDown.{u, v, w} f) = f := ULift.up_down f

/-- **The reversal on the arrow-lifted quiver**, transported from the reversal of `Q`. -/
def arrowULiftHasReverse.{u, v, w} (V : Type u) (Q : Quiver.{v, u} V)
    (R : @Quiver.HasReverse V Q) : @Quiver.HasReverse V (arrowULiftQuiver.{u, v, w} V Q) :=
  @Quiver.HasReverse.mk V (arrowULiftQuiver.{u, v, w} V Q)
    (fun {_ _} f => ⟨R.reverse' f.down⟩)

/-- **The involutive reversal on the arrow-lifted quiver**. -/
def arrowULiftHasInvolutiveReverse.{u, v, w} (V : Type u) (Q : Quiver.{v, u} V)
    (R : @Quiver.HasInvolutiveReverse V Q) :
    @Quiver.HasInvolutiveReverse V (arrowULiftQuiver.{u, v, w} V Q) :=
  @Quiver.HasInvolutiveReverse.mk V (arrowULiftQuiver.{u, v, w} V Q)
    (arrowULiftHasReverse.{u, v, w} V Q R.toHasReverse)
    (fun {a b} (f : @Quiver.Hom V (arrowULiftQuiver.{u, v, w} V Q) a b) => by
      simp only [Quiver.reverse, arrowULiftHasReverse]
      exact (congrArg ULift.up (R.inv' f.down)).trans (ULift.up_down f))

end Work.OROneRel
