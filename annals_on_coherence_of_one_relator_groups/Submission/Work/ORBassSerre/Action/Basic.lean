/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Group actions on graphs (Bass--Serre theory)

A *G-graph* is a graph (a quiver with involutive reversal) together with a `G`-action on the
vertices and on the arrows, compatible with source, target and reversal.  A *G-tree* is a
G-graph whose underlying graph is a tree (`Work.ORBassSerre.IsTree`).

## Main definitions

* `Quiver.Total.reverse` : reversal of an arrow, as an element of `Quiver.Total V`
* `Work.ORBassSerre.GraphAction` : the class of compatible `G`-actions on a graph
* `Work.ORBassSerre.IsCocompact` : finitely many orbits of vertices and of edges
-/
import Submission.Work.ORBassSerre.Tree.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v w

namespace Quiver

namespace Total

variable {V : Type u} [Quiver V]

/-- The reversed arrow, as an element of `Quiver.Total V`. -/
def reverse [Quiver.HasReverse V] (e : Total V) : Total V :=
  ⟨e.right, e.left, Quiver.reverse e.hom⟩

section HasReverse

variable [Quiver.HasReverse V]

@[simp] theorem reverse_left (e : Total V) : e.reverse.left = e.right := rfl
@[simp] theorem reverse_right (e : Total V) : e.reverse.right = e.left := rfl
@[simp] theorem reverse_hom (e : Total V) : e.reverse.hom = Quiver.reverse e.hom := rfl

@[simp] theorem reverse_mk {a b : V} (e : a ⟶ b) :
    (Total.mk a b e).reverse = Total.mk b a (Quiver.reverse e) := rfl

end HasReverse

section HasInvolutiveReverse

variable [Quiver.HasInvolutiveReverse V]

@[simp] theorem reverse_reverse (e : Total V) : e.reverse.reverse = e := by
  cases e with
  | mk l r f =>
    show Total.mk l r (Quiver.reverse (Quiver.reverse f)) = Total.mk l r f
    rw [Quiver.reverse_reverse]

end HasInvolutiveReverse

end Total

end Quiver

namespace Work.ORBassSerre

open Quiver

/-- An action of a group `G` on a graph `V`: a compatible action on the vertices and on the
arrows (i.e. on `Quiver.Total V`), commuting with reversal. -/
class GraphAction (G : Type u) (V : Type v) [Group G] [Quiver V] [Quiver.HasReverse V]
    [MulAction G V] where
  /-- The action on arrows. -/
  smulTotal : G → Quiver.Total V → Quiver.Total V
  smulTotal_one : ∀ e : Quiver.Total V, smulTotal 1 e = e
  smulTotal_mul : ∀ (g h : G) (e : Quiver.Total V), smulTotal (g * h) e = smulTotal g (smulTotal h e)
  /-- The action on arrows is compatible with the source map. -/
  smul_left : ∀ (g : G) (e : Quiver.Total V), (smulTotal g e).left = g • e.left
  /-- The action on arrows is compatible with the target map. -/
  smul_right : ∀ (g : G) (e : Quiver.Total V), (smulTotal g e).right = g • e.right
  /-- The action on arrows commutes with reversal. -/
  smul_reverse : ∀ (g : G) (e : Quiver.Total V), smulTotal g e.reverse = (smulTotal g e).reverse

variable {G : Type u} {V : Type v} [Group G] [Quiver V] [Quiver.HasReverse V] [MulAction G V]

namespace GraphAction

variable [GraphAction G V]

attribute [simp] smulTotal_one

instance : MulAction G (Quiver.Total V) where
  smul := GraphAction.smulTotal
  one_smul := GraphAction.smulTotal_one
  mul_smul := GraphAction.smulTotal_mul

@[simp] theorem smul_left_mk {a b : V} (g : G) (e : a ⟶ b) :
    (g • (Quiver.Total.mk a b e)).left = g • a := GraphAction.smul_left g _

@[simp] theorem smul_right_mk {a b : V} (g : G) (e : a ⟶ b) :
    (g • (Quiver.Total.mk a b e)).right = g • b := GraphAction.smul_right g _

@[simp] theorem smul_reverse_apply (g : G) (e : Quiver.Total V) :
    g • e.reverse = (g • e).reverse :=
  GraphAction.smul_reverse g e

theorem smul_reverse_mk {a b : V} (g : G) (e : a ⟶ b) :
    g • (Quiver.Total.mk a b e).reverse = (g • Quiver.Total.mk a b e).reverse :=
  GraphAction.smul_reverse g _

@[simp] theorem smul_mk_left {a b : V} (g : G) (e : a ⟶ b) :
    (g • Quiver.Total.mk a b e).left = g • a := smul_left_mk g e

@[simp] theorem smul_mk_right {a b : V} (g : G) (e : a ⟶ b) :
    (g • Quiver.Total.mk a b e).right = g • b := smul_right_mk g e

/-- The translate of an arrow. -/
def smulArrow (g : G) {a b : V} (e : a ⟶ b) : (g • a ⟶ g • b) :=
  Quiver.homOfEq (g • Quiver.Total.mk a b e).hom
    (GraphAction.smul_left g (Quiver.Total.mk a b e))
    (GraphAction.smul_right g (Quiver.Total.mk a b e))

theorem smulArrow_heq {a b : V} (g : G) (e : a ⟶ b) :
    HEq (smulArrow g e) (g • Quiver.Total.mk a b e).hom :=
  Quiver.homOfEq_heq _ _ _

theorem smulArrow_eq_homOfEq {a b : V} (g : G) (e : a ⟶ b) :
    smulArrow g e = Quiver.homOfEq (GraphAction.smulTotal g (Quiver.Total.mk a b e)).hom
      (GraphAction.smul_left g (Quiver.Total.mk a b e))
      (GraphAction.smul_right g (Quiver.Total.mk a b e)) := rfl

end GraphAction

/-- The action of an element `g` of the group on the graph, as a prefunctor. -/
def actionPrefunctor [GraphAction G V] (g : G) : V ⥤q V where
  obj := fun v => g • v
  map := fun {a b} e => GraphAction.smulArrow g e

@[simp] theorem actionPrefunctor_obj [GraphAction G V] (g : G) (v : V) :
    (actionPrefunctor (V := V) g).obj v = g • v := rfl

@[simp] theorem actionPrefunctor_map [GraphAction G V] (g : G) {a b : V} (e : a ⟶ b) :
    (actionPrefunctor (V := V) g).map e = GraphAction.smulArrow g e := rfl

/-- The translate of a path. -/
def smulPath [GraphAction G V] (g : G) {a b : V} (p : Quiver.Path a b) :
    Quiver.Path (g • a) (g • b) :=
  (actionPrefunctor (V := V) g).mapPath p

@[simp] theorem smulPath_nil [GraphAction G V] (g : G) (a : V) :
    smulPath g (Quiver.Path.nil : Quiver.Path a a) = Quiver.Path.nil := rfl

@[simp] theorem smulPath_cons [GraphAction G V] (g : G) {a b c : V} (p : Quiver.Path a b)
    (e : b ⟶ c) : smulPath g (p.cons e) = (smulPath g p).cons (GraphAction.smulArrow g e) := rfl

/-- A `G`-tree is a G-graph whose underlying graph is a tree. -/
def IsGTree (G : Type u) (V : Type v) [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
    [MulAction G V] [GraphAction G V] : Prop := IsTree V

/-- A `G`-graph is *cocompact* if it has finitely many orbits of vertices and of edges. -/
def IsCocompact (G : Type u) (V : Type v) [Group G] [Quiver V] [Quiver.HasReverse V]
    [MulAction G V] [GraphAction G V] : Prop :=
  Finite (MulAction.orbitRel.Quotient G V) ∧ Finite (MulAction.orbitRel.Quotient G (Quiver.Total V))

end Work.ORBassSerre

namespace Work.ORBassSerre

variable {G : Type u} {V : Type v} [Group G] [Quiver V] [Quiver.HasReverse V] [MulAction G V]

/-- The restriction of a graph action to a subgroup. -/
instance graphActionSubgroup (H : Subgroup G) [GraphAction G V] : GraphAction H V where
  smulTotal h e := GraphAction.smulTotal (h : G) e
  smulTotal_one e := by
    change GraphAction.smulTotal ((1 : H) : G) e = e
    rw [Subgroup.coe_one]
    exact GraphAction.smulTotal_one e
  smulTotal_mul g h e := by
    change GraphAction.smulTotal (((g * h : H) : G)) e =
      GraphAction.smulTotal (g : G) (GraphAction.smulTotal (h : G) e)
    rw [Subgroup.coe_mul]
    exact GraphAction.smulTotal_mul (g : G) (h : G) e
  smul_left g e := GraphAction.smul_left (g : G) e
  smul_right g e := GraphAction.smul_right (g : G) e
  smul_reverse g e := GraphAction.smul_reverse (g : G) e

end Work.ORBassSerre
