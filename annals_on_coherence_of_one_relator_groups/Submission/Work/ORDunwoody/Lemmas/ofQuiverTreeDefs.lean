/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The simple graph underlying a quiver with involutive reversal

`Work.ORBassSerre` formalizes Bass--Serre theory with *quivers* with an involutive
reversal of arrows (allowing multiple edges between two vertices), while
`Work.ORDunwoody` formalizes trees as Mathlib `SimpleGraph`s.  This file builds the
dictionary between the two: for a quiver `V` with involutive reversal and no loops, the
underlying simple graph `quiverGraph V hnl` has `Adj u v := Nonempty (u ⟶ v)`.

The two directions between walks in this simple graph and paths in the quiver are
`ofWalk` (choose an arrow for every step) and `toWalk` (forget the arrows along a path).

## Main definitions

* `Work.ORDunwoody.Lemmas.quiverGraph`
* `Work.ORDunwoody.Lemmas.ofWalk`
* `Work.ORDunwoody.Lemmas.toWalk`
-/
import Mathlib
import Submission.Work.ORDunwoody.Basic
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree

set_option autoImplicit false

set_option linter.unusedVariables false

universe u v w

namespace Work.ORDunwoody.Lemmas

open Quiver

/-- The simple graph underlying a quiver with involutive reversal: two vertices are adjacent
when there is an arrow between them.  The hypothesis `hnl` (no loops) is what makes this
relation irreflexive; in the applications it is supplied by the tree hypothesis. -/
abbrev quiverGraph (V : Type v) [Quiver V] [Quiver.HasInvolutiveReverse V]
    (hnl : ∀ u : V, ¬ Nonempty (u ⟶ u)) : SimpleGraph V where
  Adj u v := Nonempty (u ⟶ v)
  symm := ⟨fun _ _ h => h.elim fun e => ⟨Quiver.reverse e⟩⟩
  loopless := ⟨fun u h => hnl u h⟩

@[simp] theorem quiverGraph_adj {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hnl : ∀ u : V, ¬ Nonempty (u ⟶ u)} (u v : V) :
    (quiverGraph V hnl).Adj u v ↔ Nonempty (u ⟶ v) := Iff.rfl

/-- The path in the quiver induced by a walk in the underlying simple graph, by choosing an
arrow for every step of the walk. -/
noncomputable def ofWalk {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hnl : ∀ u : V, ¬ Nonempty (u ⟶ u)} {a b : V} :
    (quiverGraph V hnl).Walk a b → Quiver.Path a b
  | .nil => Quiver.Path.nil
  | .cons h p => (Quiver.Path.nil.cons (Classical.choice h)).comp (ofWalk p)

/-- The walk in the underlying simple graph induced by a path in the quiver. -/
def toWalk {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hnl : ∀ u : V, ¬ Nonempty (u ⟶ u)} {a b : V} :
    Quiver.Path a b → (quiverGraph V hnl).Walk a b
  | .nil => .nil
  | .cons p e => (toWalk p).concat ⟨e⟩

@[simp] theorem ofWalk_nil {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hnl : ∀ u : V, ¬ Nonempty (u ⟶ u)} {a : V} :
    ofWalk (hnl := hnl) (SimpleGraph.Walk.nil : (quiverGraph V hnl).Walk a a) =
      Quiver.Path.nil := rfl

theorem ofWalk_cons {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hnl : ∀ u : V, ¬ Nonempty (u ⟶ u)} {a b c : V}
    (h : (quiverGraph V hnl).Adj a b) (p : (quiverGraph V hnl).Walk b c) :
    ofWalk (hnl := hnl) (.cons h p) =
      (Quiver.Path.nil.cons (Classical.choice h)).comp (ofWalk (hnl := hnl) p) := rfl

@[simp] theorem toWalk_nil {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hnl : ∀ u : V, ¬ Nonempty (u ⟶ u)} {a : V} :
    toWalk (hnl := hnl) (Quiver.Path.nil : Quiver.Path a a) =
      (SimpleGraph.Walk.nil : (quiverGraph V hnl).Walk a a) := rfl

theorem toWalk_cons {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hnl : ∀ u : V, ¬ Nonempty (u ⟶ u)} {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c) :
    toWalk (hnl := hnl) (p.cons e) =
      (toWalk (hnl := hnl) p).concat (show (quiverGraph V hnl).Adj b c from ⟨e⟩) := rfl

/-- The length of the induced path is the length of the walk. -/
theorem ofWalk_length {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hnl : ∀ u : V, ¬ Nonempty (u ⟶ u)} {a b : V}
    (p : (quiverGraph V hnl).Walk a b) :
    (ofWalk (hnl := hnl) p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [ofWalk_cons, Quiver.Path.length_comp, Quiver.Path.length_cons,
      Quiver.Path.length_nil, ih, SimpleGraph.Walk.length_cons]
    omega

/-- The vertices of the induced path are the vertices visited by the walk. -/
theorem vertices_ofWalk {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hnl : ∀ u : V, ¬ Nonempty (u ⟶ u)} {a b : V}
    (p : (quiverGraph V hnl).Walk a b) :
    (ofWalk (hnl := hnl) p).vertices = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [ofWalk_cons, Quiver.Path.vertices_comp, Quiver.Path.vertices_cons,
      SimpleGraph.Walk.support_cons, ih]
    simp

/-- The vertices of a path in which one backtrack has been inserted next to a subpath
`p₂` starting at `x`. -/
theorem vertices_comp_backtrack {V : Type v} [Quiver V] [Quiver.HasReverse V]
    {a x y b : V} (p₁ : Quiver.Path a x) (e : x ⟶ y) (p₂ : Quiver.Path x b) :
    (p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂))).vertices =
      p₁.vertices.dropLast ++ [x, y] ++ p₂.vertices := by
  have h1 : (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)).vertices
      = [x, y] ++ p₂.vertices := by
    simp [Quiver.Path.vertices_comp, Quiver.Path.vertices_toPath, List.append_assoc]
  rw [Quiver.Path.vertices_comp, h1, List.append_assoc]

end Work.ORDunwoody.Lemmas
