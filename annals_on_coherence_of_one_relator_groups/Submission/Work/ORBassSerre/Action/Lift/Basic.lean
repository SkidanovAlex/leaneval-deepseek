/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lifting a `G`-tree to a universe where the arrows live with the group

The Bass--Serre presentation machinery (`Submission.Work.ORBassSerre.Action.Structure.*`)
indexes edge orbits by `Work.ORBassSerre.orbitE G V`, whose declared universe is pinned in such a
way that it can only be used when the arrows of `V` live in the *same universe* as the group `G`.
Theorems stated in terms of `orbitE` therefore carry the (implicit) universe constraint
`univ(arrows of V) = univ(G)`.

The present file removes that constraint by *lifting the whole situation to a common universe*:
given `G : Type u`, `V : Type v` and arrows of `V` in `Type w`, we build

* the lifted vertex type `VLx G V = ULift.{max u v w} V`;
* the lifted quiver on `VLx G V` whose arrows are the arrows of `V` lifted to the universe
  `max u v w` (`instQuiver`), with reversal `instHasInvolutiveReverse`;
* the lifted group `LGroup G V = ULift.{max u v w} G`, which lives in the *same* universe
  `max u v w` as the lifted arrows;
* the lifted action of the lifted group on the lifted vertices (`instMulAction`) and on the
  lifted graph (`instGraphAction`).

Because the universe level `max u v w` is *determined* by the arguments `G`, `V` and the ambient
arrow type, all of these are ordinary global instances, so the lifted structure can be referred
to by typeclass inference.

Thus a `G`-tree on `V` can be traded for an `LGroup G V`-tree on `VLx G V`, on which the pinned
`orbitE` applies, and the structure transfers back along the bijections
(proved in companion files): `IsTree`, `IsCocompact`, vertex stabilisers and edge stabilisers are
all preserved, and `Group.IsFinitelyPresented` descends along `LGroup G V ≃* G`.

## Main definitions

* `Work.ORBassSerre.Action.Lift.VLx` : the vertex type of the lifted graph
* `Work.ORBassSerre.Action.Lift.instQuiver` : the lifted quiver
* `Work.ORBassSerre.Action.Lift.instHasInvolutiveReverse` : reversal on the lifted quiver
* `Work.ORBassSerre.Action.Lift.LGroup` : the lifted group
* `Work.ORBassSerre.Action.Lift.instMulAction` : the lifted action on vertices
* `Work.ORBassSerre.Action.Lift.instGraphAction` : the lifted action on the lifted graph
-/
import Mathlib
import Submission.Work.ORBassSerre.Action.Basic

/-!
## The transfer lemmas (proved in companion files)

The structure of `V` transfers to the lifted graph along the bijections `VLx.equiv` and
`totalEquiv`, and the resulting statements are:

* `Work.ORBassSerre.Action.Lift.isTree_VLx` : `IsTree V → IsTree (VLx G V)`.
  Proof: the prefunctors `V ⥤q VLx G V` (`obj := VLx.up`, `map := ULift.up`) and
  `VLx G V ⥤q V` (`obj := VLx.down = ULift.down`, `map := ULift.down`) are mutually inverse on
  objects and arrows; paths and their reducedness transfer along them, so connectivity and
  "no non-trivial reduced closed path" transfer.  (`Prefunctor.mapPath`, `Path.IsReduced`,
  `Quiver.Path.DeleteBacktrack`; the workspace lemmas
  `Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced` and `qpath_mapPath_reverse` help.)

* `Work.ORBassSerre.Action.Lift.isCocompact_VLx` : `IsCocompact G V → IsCocompact (LGroup G V) (VLx G V)`.
  Proof: the equivariant bijections `VLx.equiv` and `totalEquiv` induce bijections of the orbit
  sets (`Quotient.map`/`Quotient.lift`), so finiteness transfers; note
  `(u : LGroup G V) • a = VLx.up (u.down • a.down)` and `totalEquiv` commutes with the actions.

* `Work.ORBassSerre.Action.Lift.isFinitelyPresented_stabilizer_VLx` :
  `(∀ v, IsFinitelyPresented (stabilizer G v)) → ∀ a : VLx G V,
  IsFinitelyPresented (stabilizer (LGroup G V) a)`.
  Proof: `stabilizer (LGroup G V) a ≃* stabilizer G a.down` (an explicit `MulEquiv`), so
  finite presentability transfers (`Group.IsFinitelyPresented.equiv` /
  `Group.IsFinitelyPresented.of_surjective`).

* `Work.ORBassSerre.Action.Lift.fg_stabilizer_VLx` :
  `(∀ e : Quiver.Total V, Group.FG (stabilizer G e)) → ∀ e' : Quiver.Total (VLx G V),
  Group.FG (stabilizer (LGroup G V) e')`.
  Proof: `stabilizer (LGroup G V) e' ≃* stabilizer G (totalEquiv G V e')` (use
  `totalEquiv_apply`, `totalEquiv_symm_apply`, `GraphAction.smul_left`, `GraphAction.smul_right`),
  and `Group.FG` transfers along a surjective homomorphism (`Group.fg_of_surjective`).

* `Work.ORBassSerre.Action.Lift.isFinitelyPresented_of_LGroup` :
  `IsFinitelyPresented (LGroup G V) → IsFinitelyPresented G`.
  Proof: `LGroupEquiv G V : LGroup G V ≃* G`, using `Group.IsFinitelyPresented.of_surjective`
  with the trivial kernel.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

universe u v w

namespace Work.ORBassSerre.Action.Lift

open Quiver

/-- Two elements of a `ULift` are equal as soon as their underlying elements are. -/
theorem ulift_eq_of_down_eq {α : Type*} {x y : ULift α} (h : x.down = y.down) : x = y := by
  rw [← ULift.up_down x, ← ULift.up_down y, h]

/-! ## The lifted vertex type -/

/-- The vertex type of the lifted graph: the vertices of `V`, lifted to the universe
`max u v w` of the lifted group and of the lifted arrows.  The argument `G : Type u` only records
that universe level. -/
def VLx (G : Type u) (V : Type v) [Quiver.{w, v} V] : Type (max u v w) := ULift.{max u v w} V

namespace VLx

variable {G : Type u} {V : Type v} [Quiver.{w, v} V]

/-- The canonical vertex of the lifted graph over a vertex of `V`. -/
abbrev up (v : V) : VLx G V := ULift.up v

@[simp] theorem down_up (v : V) : (VLx.up (G := G) v).down = v := rfl

@[simp] theorem up_down (a : VLx G V) : VLx.up (G := G) a.down = a := ULift.up_down a

theorem ext {a b : VLx G V} (h : a.down = b.down) : a = b := by
  rw [← up_down (G := G) a, ← up_down (G := G) b, h]

/-- The bijection between the lifted vertices and the vertices of `V`. -/
def equiv (G : Type u) (V : Type v) [Quiver.{w, v} V] : VLx G V ≃ V where
  toFun := fun a => a.down
  invFun := fun v => ULift.up v
  left_inv := fun a => up_down a
  right_inv := fun _ => rfl

end VLx

/-! ## The lifted graph -/

/-- The lifted quiver on `VLx G V`: the arrows of `V`, lifted to the universe `max u v w` of the
lifted group. -/
instance instQuiver (G : Type u) (V : Type v) [Quiver.{w, v} V] : Quiver (VLx G V) where
  Hom a b := ULift.{max u v w} (a.down ⟶ b.down)

theorem quiver_hom_eq (G : Type u) (V : Type v) [Quiver.{w, v} V] (a b : VLx G V) :
    (a ⟶ b) = ULift.{max u v w} (a.down ⟶ b.down) := rfl

/-- Reversal on the lifted quiver, lifted from the reversal of `V`. -/
instance instHasReverse (G : Type u) (V : Type v) [Quiver.{w, v} V] [Quiver.HasReverse V] :
    Quiver.HasReverse (VLx G V) where
  reverse' := fun {_ _} f => ULift.up (Quiver.reverse (V := V) f.down)

@[simp] theorem reverse_apply (G : Type u) (V : Type v) [Quiver.{w, v} V] [Quiver.HasReverse V]
    {a b : VLx G V} (f : a ⟶ b) :
    Quiver.reverse f = ULift.up (Quiver.reverse (V := V) f.down) := rfl

/-- Reversal on the lifted quiver is involutive. -/
instance instHasInvolutiveReverse (G : Type u) (V : Type v) [Quiver.{w, v} V]
    [Quiver.HasInvolutiveReverse V] : Quiver.HasInvolutiveReverse (VLx G V) where
  toHasReverse := instHasReverse G V
  inv' := by
    intro a b f
    apply ulift_eq_of_down_eq
    exact Quiver.reverse_reverse (V := V) f.down

/-! ## The lifted group and its action -/

/-- The group `G` lifted to the universe `max u v w` of the lifted arrows. -/
abbrev LGroup (G : Type u) (V : Type v) [Quiver.{w, v} V] : Type (max u v w) :=
  ULift.{max u v w} G

/-- The group structure on the lifted group.

This is an `abbrev`, not an `instance`: `LGroup G V` is `ULift G`, so as an instance it matches
*every* goal of the form `Group (ULift α)` (and hence every `Group (ULift …)` goal anywhere in
the workspace), and since `V` is not determined by the goal Lean then searches `Quiver ?V`, which
diverges.  As a reducible `def` the underlying `ULift.group` instance is still found by ordinary
reducible unfolding, but this declaration is no longer tried by instance search. -/
abbrev instGroupLGroup (G : Type u) (V : Type v) [Quiver.{w, v} V] [Group G] :
    Group (LGroup G V) := inferInstanceAs (Group (ULift.{max u v w} G))

/-- The canonical isomorphism between the lifted group and `G`. -/
def LGroupEquiv (G : Type u) (V : Type v) [Quiver.{w, v} V] [Group G] : LGroup G V ≃* G :=
  MulEquiv.ulift

section Action

variable {G : Type u} {V : Type v} [Quiver.{w, v} V] [Group G] [MulAction G V]

/-- The lifted action of the lifted group on the lifted vertices. -/
instance instMulAction : MulAction (LGroup G V) (VLx G V) where
  smul g a := VLx.up (g.down • a.down)
  one_smul a := by
    cases a with
    | up v =>
      show VLx.up ((1 : ULift.{max u v w} G).down • v) = VLx.up v
      rw [show (1 : ULift.{max u v w} G).down = (1 : G) from rfl, one_smul]
  mul_smul g h a := by
    cases a with
    | up v =>
      show VLx.up (((g * h : ULift.{max u v w} G)).down • v) = VLx.up (g.down • (h.down • v))
      rw [show (g * h : ULift.{max u v w} G).down = g.down * h.down from rfl, mul_smul]

@[simp] theorem smul_VLx (g : LGroup G V) (a : VLx G V) :
    g • a = VLx.up (g.down • a.down) := rfl

end Action

/-! ## The bijection between the arrows of the lifted graph and the arrows of `V` -/

/-- The arrows of the lifted graph correspond to the arrows of `V`. -/
def totalEquiv (G : Type u) (V : Type v) [Quiver.{w, v} V] :
    Quiver.Total (VLx G V) ≃ Quiver.Total V where
  toFun e := ⟨e.left.down, e.right.down, e.hom.down⟩
  invFun e := ⟨VLx.up e.left, VLx.up e.right, ULift.up e.hom⟩
  left_inv e := by
    cases e with
    | mk l r f =>
      cases l with | up lv =>
      cases r with | up rv =>
      change ULift.{max u v w} (lv ⟶ rv) at f
      cases f with | up f => rfl
  right_inv e := by
    cases e with
    | mk l r f => rfl

@[simp] theorem totalEquiv_apply (G : Type u) (V : Type v) [Quiver.{w, v} V]
    (e : Quiver.Total (VLx G V)) :
    totalEquiv G V e = ⟨e.left.down, e.right.down, e.hom.down⟩ := rfl

@[simp] theorem totalEquiv_symm_apply (G : Type u) (V : Type v) [Quiver.{w, v} V]
    (e : Quiver.Total V) :
    (totalEquiv G V).symm e = ⟨VLx.up e.left, VLx.up e.right, ULift.up e.hom⟩ := rfl

theorem totalEquiv_symm_reverse (G : Type u) (V : Type v) [Quiver.{w, v} V]
    [Quiver.HasInvolutiveReverse V] (e : Quiver.Total V) :
    (totalEquiv G V).symm e.reverse = ((totalEquiv G V).symm e).reverse := by
  cases e with
  | mk l r f => rfl

section GraphAction

variable {G : Type u} {V : Type v} [Quiver.{w, v} V] [Quiver.HasInvolutiveReverse V]
  [Group G] [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-- The lifted graph action: the lifted group acts on the lifted graph through the action of `G`
on `V`, transported along the bijection of arrows. -/
instance instGraphAction : Work.ORBassSerre.GraphAction (LGroup G V) (VLx G V) where
  smulTotal g e := (totalEquiv G V).symm (g.down • totalEquiv G V e)
  smulTotal_one e := by
    show (totalEquiv G V).symm ((1 : LGroup G V).down • totalEquiv G V e) = e
    rw [show (1 : LGroup G V).down = (1 : G) from rfl, one_smul]
    exact (totalEquiv G V).symm_apply_apply e
  smulTotal_mul g h e := by
    show (totalEquiv G V).symm (((g * h : LGroup G V)).down • totalEquiv G V e) =
      (totalEquiv G V).symm (g.down • totalEquiv G V ((totalEquiv G V).symm (h.down • totalEquiv G V e)))
    rw [show ((g * h : LGroup G V)).down = g.down * h.down from rfl, mul_smul,
      (totalEquiv G V).apply_symm_apply]
  smul_left g e := by
    show ((totalEquiv G V).symm (g.down • totalEquiv G V e)).left = g • e.left
    simp only [totalEquiv_symm_apply]
    have hX : (g.down • totalEquiv G V e).left = g.down • e.left.down := by
      show (GraphAction.smulTotal g.down (totalEquiv G V e)).left = g.down • e.left.down
      rw [GraphAction.smul_left]
      rfl
    rw [hX]
    rfl
  smul_right g e := by
    show ((totalEquiv G V).symm (g.down • totalEquiv G V e)).right = g • e.right
    simp only [totalEquiv_symm_apply]
    have hX : (g.down • totalEquiv G V e).right = g.down • e.right.down := by
      show (GraphAction.smulTotal g.down (totalEquiv G V e)).right = g.down • e.right.down
      rw [GraphAction.smul_right]
      rfl
    rw [hX]
    rfl
  smul_reverse g e := by
    show (totalEquiv G V).symm (g.down • totalEquiv G V e.reverse) =
      ((totalEquiv G V).symm (g.down • totalEquiv G V e)).reverse
    have hev : totalEquiv G V e.reverse = (totalEquiv G V e).reverse := by
      cases e with
      | mk l r f =>
        cases l with | up lv =>
        cases r with | up rv =>
        change ULift.{max u v w} (lv ⟶ rv) at f
        cases f with | up f => rfl
    have hsm : g.down • totalEquiv G V e.reverse = (g.down • totalEquiv G V e).reverse := by
      rw [hev]
      exact GraphAction.smul_reverse g.down (totalEquiv G V e)
    rw [hsm]
    exact totalEquiv_symm_reverse G V (g.down • totalEquiv G V e)

@[simp] theorem smulTotal_VLx_apply (g : LGroup G V) (e : Quiver.Total (VLx G V)) :
    g • e = (totalEquiv G V).symm (g.down • totalEquiv G V e) := rfl

end GraphAction

end Work.ORBassSerre.Action.Lift
