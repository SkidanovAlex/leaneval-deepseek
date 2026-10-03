import Mathlib
import Submission.Work.OROneRel.arrowULift
import Submission.Work.ORBassSerre.Interface

set_option warn.classDefReducibility false

namespace Work.OROneRel

open Quiver

universe u v w

/-! ## Prefunctors between `Q` and its arrow-`ULift`

The arrow-`ULift` quiver `arrowULiftQuiver V Q` has the same vertices as `Q`, but its arrows are
obtained by `ULift`ing the arrows of `Q` (into the universe `max v w`).  Because the two quivers
live on the *same* type `V`, the two associated `Quiver` instances coexist in the same context;
all the helper statements below therefore carry their instance arguments explicitly.

The two prefunctors are mutually inverse on arrows and commute with reversal, hence they transport
reduced paths (and with them tree-ness) in both directions. -/

/-- The tautological prefunctor `Q ⥤ arrowULiftQuiver V Q` (the identity on vertices). -/
def arrowULiftPF (V : Type u) (Q : Quiver.{v, u} V) :
    @Prefunctor V Q V (arrowULiftQuiver.{u, v, w} V Q) :=
  @Prefunctor.mk V Q V (arrowULiftQuiver.{u, v, w} V Q) id
    (fun {_ _} f => arrowULiftUp.{u, v, w} f)

/-- The inverse prefunctor `arrowULiftQuiver V Q ⥤ Q` (the identity on vertices). -/
def arrowULiftDownPF (V : Type u) (Q : Quiver.{v, u} V) :
    @Prefunctor V (arrowULiftQuiver.{u, v, w} V Q) V Q :=
  @Prefunctor.mk V (arrowULiftQuiver.{u, v, w} V Q) V Q id
    (fun {_ _} f => arrowULiftDown.{u, v, w} f)

/-- The prefunctor out of the arrow-`ULift` commutes with reversal. -/
theorem arrowULiftDownPF_mapReverse (V : Type u) (Q : Quiver.{v, u} V)
    (R : @Quiver.HasInvolutiveReverse V Q) :
    @Prefunctor.MapReverse V V (arrowULiftQuiver.{u, v, w} V Q) Q
      (arrowULiftHasReverse.{u, v, w} V Q R.toHasReverse) R.toHasReverse
      (arrowULiftDownPF.{u, v, w} V Q) :=
  @Prefunctor.MapReverse.mk V V (arrowULiftQuiver.{u, v, w} V Q) Q
    (arrowULiftHasReverse.{u, v, w} V Q R.toHasReverse) R.toHasReverse
    (arrowULiftDownPF.{u, v, w} V Q)
    (fun {_ _} _ => rfl)

/-- A reduced path in the arrow-`ULift` pushes down to a reduced path in the original graph. -/
theorem arrowULift_isReduced_down (V : Type u) (Q : Quiver.{v, u} V)
    (R : @Quiver.HasInvolutiveReverse V Q) {a b : V}
    {p : @Quiver.Path V (arrowULiftQuiver.{u, v, w} V Q) a b}
    (hp : @Quiver.Path.IsReduced V (arrowULiftQuiver.{u, v, w} V Q) a b
      (arrowULiftHasReverse.{u, v, w} V Q R.toHasReverse) p) :
    @Quiver.Path.IsReduced V Q a b R.toHasReverse
      (@Prefunctor.mapPath V (arrowULiftQuiver.{u, v, w} V Q) V Q
        (arrowULiftDownPF.{u, v, w} V Q) a b p) :=
  @Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced V V
    (arrowULiftQuiver.{u, v, w} V Q) (arrowULiftHasReverse.{u, v, w} V Q R.toHasReverse)
    Q R.toHasReverse (arrowULiftDownPF.{u, v, w} V Q)
    (arrowULiftDownPF_mapReverse.{u, v, w} V Q R)
    Function.injective_id
    (fun {_ _} x y h =>
      ULift.down_inj.mp (h : arrowULiftDown.{u, v, w} x = arrowULiftDown.{u, v, w} y))
    a b p hp

/-- The forgetful prefunctor preserves the length of a path. -/
theorem arrowULiftDownPF_mapPath_length (V : Type u) (Q : Quiver.{v, u} V) {a b : V}
    (p : @Quiver.Path V (arrowULiftQuiver.{u, v, w} V Q) a b) :
    @Quiver.Path.length V Q a b
        (@Prefunctor.mapPath V (arrowULiftQuiver.{u, v, w} V Q) V Q
          (arrowULiftDownPF.{u, v, w} V Q) a b p)
      = @Quiver.Path.length V (arrowULiftQuiver.{u, v, w} V Q) a b p := by
  induction p with
  | nil => exact @Quiver.Path.length_nil V Q a
  | cons p e ih =>
      show Nat.succ (@Quiver.Path.length V Q _ _
              (@Prefunctor.mapPath V (arrowULiftQuiver.{u, v, w} V Q) V Q
                (arrowULiftDownPF.{u, v, w} V Q) _ _ p))
          = Nat.succ (@Quiver.Path.length V (arrowULiftQuiver.{u, v, w} V Q) _ _ p)
      exact congrArg Nat.succ ih

/-! ## Transport of `IsTree` -/

theorem isTree_arrowULift {V : Type u} {Q : Quiver.{v, u} V} (R : @Quiver.HasInvolutiveReverse V Q) (h : @Work.ORBassSerre.IsTree V Q R) : @Work.ORBassSerre.IsTree V (Work.OROneRel.arrowULiftQuiver V Q) (Work.OROneRel.arrowULiftHasInvolutiveReverse V Q R) := by
  obtain ⟨hconn, hacyc⟩ := h
  refine ⟨?_, ?_⟩
  · intro a b
    obtain ⟨p⟩ := hconn a b
    exact ⟨@Prefunctor.mapPath V Q V (arrowULiftQuiver V Q) (arrowULiftPF V Q) a b p⟩
  · intro a p hp
    have hq := arrowULift_isReduced_down V Q R hp
    have hnil : @Prefunctor.mapPath V (arrowULiftQuiver V Q) V Q
        (arrowULiftDownPF V Q) a a p = @Quiver.Path.nil V Q a := hacyc a _ hq
    have hlen : @Quiver.Path.length V (arrowULiftQuiver V Q) a a p = 0 := by
      have hlen' := arrowULiftDownPF_mapPath_length V Q p
      rw [hnil, Quiver.Path.length_nil] at hlen'
      exact hlen'.symm
    exact @Quiver.Path.eq_nil_of_length_zero V (arrowULiftQuiver V Q) a p hlen

end Work.OROneRel
