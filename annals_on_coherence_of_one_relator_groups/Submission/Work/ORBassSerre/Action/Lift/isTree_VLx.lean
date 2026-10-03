/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The lift of a tree is a tree

`VLx G V` is the graph with the same vertices and arrows as `V`, all of them moved to the common
universe `max u v w` of the group and of the arrows.  The morphisms `ULift.up` and `ULift.down`
give mutually inverse morphisms of graphs (`prefunctorUp`, `prefunctorDown`), so connectivity and
"no non-trivial reduced closed path" transfer: `VLx G V` is a tree as soon as `V` is.
-/
import Mathlib
import Submission.Work.ORBassSerre.Action.Lift.Basic
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u v w

namespace Work.ORBassSerre.Action.Lift

open Quiver

variable {G : Type u} {V : Type v} [Quiver.{w, v} V]

/-- The graph morphism `V ⥤q VLx G V`, lifting vertices and arrows along `ULift.up`. -/
def prefunctorUp (G : Type u) (V : Type v) [Quiver.{w, v} V] : V ⥤q VLx G V where
  obj v := VLx.up v
  map f := ULift.up f

/-- The graph morphism `VLx G V ⥤q V`, lowering vertices and arrows along `ULift.down`. -/
def prefunctorDown (G : Type u) (V : Type v) [Quiver.{w, v} V] : VLx G V ⥤q V where
  obj a := a.down
  map f := f.down

@[simp]
theorem prefunctorUp_obj (v : V) : (prefunctorUp G V).obj v = VLx.up v := rfl

@[simp]
theorem prefunctorUp_map {a b : V} (f : a ⟶ b) :
    (prefunctorUp G V).map f = ULift.up f := rfl

@[simp]
theorem prefunctorDown_obj (a : VLx G V) : (prefunctorDown G V).obj a = a.down := rfl

@[simp]
theorem prefunctorDown_map {a b : VLx G V} (f : a ⟶ b) :
    (prefunctorDown G V).map f = f.down := rfl

/-- `ULift.up` is injective on the vertices of `V`. -/
theorem prefunctorUp_obj_injective : Function.Injective (prefunctorUp G V).obj :=
  fun _ _ h => ULift.up_injective h

/-- `ULift.down` is injective on the vertices of the lifted graph. -/
theorem prefunctorDown_obj_injective : Function.Injective (prefunctorDown G V).obj :=
  fun _ _ h => ULift.ext h

instance instMapReversePrefunctorUp [Quiver.HasReverse V] :
    (prefunctorUp G V).MapReverse where
  map_reverse' _ := rfl

instance instMapReversePrefunctorDown [Quiver.HasReverse V] :
    (prefunctorDown G V).MapReverse where
  map_reverse' _ := rfl

/-- Lifting a path and then lowering it returns the original path. -/
theorem mapPath_up_down {a b : VLx G V} (p : Quiver.Path a b) :
    (prefunctorUp G V).mapPath ((prefunctorDown G V).mapPath p) = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    show Quiver.Path.cons ((prefunctorUp G V).mapPath ((prefunctorDown G V).mapPath p))
      ((prefunctorUp G V).map ((prefunctorDown G V).map e)) = Quiver.Path.cons p e
    rw [ih]
    rfl

theorem isTree_VLx {G : Type*} {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (hT : Work.ORBassSerre.IsTree V) :
    Work.ORBassSerre.IsTree (Work.ORBassSerre.Action.Lift.VLx G V) := by
  refine ⟨?_, ?_⟩
  · intro a b
    obtain ⟨p⟩ := hT.1 a.down b.down
    exact ⟨(prefunctorUp G V).mapPath p⟩
  · intro a p hp
    have hred : ((prefunctorDown G V).mapPath p).IsReduced :=
      Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced (prefunctorDown G V)
        prefunctorDown_obj_injective
        (fun {_ _} x y h => ULift.ext (x := x) (y := y) h) hp
    have hnil := hT.2 a.down ((prefunctorDown G V).mapPath p) hred
    rw [← mapPath_up_down p]
    rw [hnil]
    exact Prefunctor.mapPath_nil (prefunctorUp G V) a.down

end Work.ORBassSerre.Action.Lift
