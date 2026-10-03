/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quotient graph of a `G`-graph

For a group `G` acting on a graph `V` (a `Work.ORBassSerre.GraphAction`), the quotient graph
`V/G` has vertices the `G`-orbits of vertices and arrows the `G`-orbits of arrows whose
endpoints have the prescribed orbits.  The quotient map is a prefunctor
`Quiver.Prefunctor V (V/G)` preserving reversal.

## Main definitions

* `Work.ORBassSerre.orbitV` : the orbit set of vertices
* `Work.ORBassSerre.orbitE` : the orbit set of edges
* `Work.ORBassSerre.orbitQuiver` : the quotient graph
* `Work.ORBassSerre.orbitPrefunctor` : the quotient map
* `Work.ORBassSerre.ActsFreely` : the action has no non-trivial vertex stabiliser
-/
import Submission.Work.ORBassSerre.Action.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v w

namespace Work.ORBassSerre

open Quiver

variable {G : Type u} {V : Type v} [Group G] [Quiver V] [Quiver.HasReverse V] [MulAction G V]
  [GraphAction G V]

/-- The set of orbits of vertices of a `G`-graph. -/
abbrev orbitV (G : Type u) (V : Type v) [Group G] [Quiver V] [MulAction G V] : Type v :=
  MulAction.orbitRel.Quotient G V

/-- The set of orbits of arrows of a `G`-graph. -/
abbrev orbitE (G : Type u) (V : Type v) [Group G] [Quiver V] [MulAction G V]
    [Quiver.HasReverse V] [GraphAction G V] : Type (max u v) :=
  MulAction.orbitRel.Quotient G (Quiver.Total V)

/-- Reversal of arrows commutes with the action, hence induces a map on orbits. -/
theorem orbitRel_reverse {e f : Quiver.Total V}
    (h : MulAction.orbitRel G (Quiver.Total V) e f) :
    MulAction.orbitRel G (Quiver.Total V) e.reverse f.reverse := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, (GraphAction.smul_reverse_apply g f).trans (congrArg Quiver.Total.reverse hg)⟩

/-- Reversal of orbits of arrows. -/
def orbitEReverse (E : orbitE G V) : orbitE G V :=
  Quotient.map Quiver.Total.reverse (fun _ _ h => orbitRel_reverse h) E

@[simp] theorem orbitEReverse_mk (e : Quiver.Total V) :
    orbitEReverse (G := G) (V := V) (Quotient.mk'' e) = Quotient.mk'' e.reverse :=
  Quotient.map_mk _ _ _

/-- The quotient graph `V/G`: vertices are orbits of vertices, arrows are orbits of arrows whose
source and target have the prescribed orbits. -/
instance orbitQuiver : Quiver (orbitV G V) where
  Hom A B := {E : orbitE G V //
    ∃ e : Quiver.Total V, Quotient.mk'' e = E ∧ Quotient.mk'' e.left = A ∧
      Quotient.mk'' e.right = B}

instance orbitHasReverse : Quiver.HasReverse (orbitV G V) where
  reverse' := fun {A B} E => ⟨orbitEReverse E.1, by
    obtain ⟨e, he, hl, hr⟩ := E.2
    refine ⟨e.reverse, ?_, ?_, ?_⟩
    · rw [← he, orbitEReverse_mk]
    · show Quotient.mk'' e.reverse.left = B
      rw [Quiver.Total.reverse_left, hr]
    · show Quotient.mk'' e.reverse.right = A
      rw [Quiver.Total.reverse_right, hl]⟩

/-- The orbit class of an arrow, as an arrow of the quotient graph. -/
def orbitArrow {a b : V} (e : a ⟶ b) :
    (Quotient.mk'' a : orbitV G V) ⟶ Quotient.mk'' b :=
  ⟨Quotient.mk'' (Quiver.Total.mk a b e), ⟨Quiver.Total.mk a b e, rfl, rfl, rfl⟩⟩

@[simp] theorem orbitArrow_val {a b : V} (e : a ⟶ b) :
    (orbitArrow (G := G) e).1 = Quotient.mk'' (Quiver.Total.mk a b e) := rfl

/-- The quotient map as a prefunctor. -/
def orbitPrefunctor : V ⥤q orbitV G V where
  obj := Quotient.mk''
  map := fun {a b} e => orbitArrow (G := G) e

@[simp] theorem orbitPrefunctor_obj (v : V) :
    (orbitPrefunctor (G := G) (V := V)).obj v = Quotient.mk'' v := rfl
@[simp] theorem orbitPrefunctor_map {a b : V} (e : a ⟶ b) :
    (orbitPrefunctor (G := G) (V := V)).map e = orbitArrow (G := G) e := rfl

theorem orbitPrefunctor_mapReverse : (orbitPrefunctor (G := G) (V := V)).MapReverse where
  map_reverse' := fun e => by
    apply Subtype.ext
    change Quotient.mk'' (Quiver.Total.mk _ _ (Quiver.reverse e)) =
      orbitEReverse (Quotient.mk'' (Quiver.Total.mk _ _ e))
    rw [orbitEReverse_mk]
    rfl

/-- The action of `G` on a graph is free if no non-trivial element fixes a vertex. -/
def ActsFreely (G : Type u) (V : Type v) [Group G] [MulAction G V] : Prop :=
  ∀ (g : G) (v : V), g • v = v → g = 1

theorem actsFreely_iff_stabilizer_bot {G : Type u} {V : Type v} [Group G] [MulAction G V] :
    ActsFreely G V ↔ ∀ v : V, MulAction.stabilizer G v = ⊥ := by
  constructor
  · intro h v
    ext g
    simp only [Subgroup.mem_bot, MulAction.mem_stabilizer_iff]
    exact ⟨fun hg => h g v hg, fun hg => by rw [hg, one_smul]⟩
  · intro h g v hv
    have : g ∈ MulAction.stabilizer G v := hv
    rw [h v] at this
    exact this

end Work.ORBassSerre
