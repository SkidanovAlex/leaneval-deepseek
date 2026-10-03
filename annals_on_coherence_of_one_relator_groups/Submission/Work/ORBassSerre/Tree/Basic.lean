/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Graphs, paths and trees (Bass--Serre theory, foundations)

A *graph* in this development is a `Quiver` (a directed multigraph) equipped with an
involutive reversal of arrows, i.e. `Quiver.HasInvolutiveReverse`.  This is exactly a
simplicial graph in the sense of Bass--Serre theory, allowing multiple edges between two
vertices (which is essential: the Bass--Serre tree of `HNN(G,1,1,1)` has two vertices
joined by infinitely many edges).

Paths are `Quiver.Path`.  A path is *reduced* if it contains no backtrack, i.e. no two
consecutive arrows that are mutually inverse.  A graph is a *tree* if it is connected and
has no non-trivial reduced closed path.  (This is equivalent to the standard definition
"connected and simply connected"; unique reduced paths are derived in
`Submission/Work/ORBassSerre/Tree/Geodesic.lean`.)

## Main definitions

* `Quiver.Path.DeleteBacktrack` : deleting a backtrack from a path
* `Quiver.Path.ReducesTo` : the reflexive-transitive closure of backtrack deletion
* `Quiver.Path.IsReduced` : a path with no backtrack
* `Work.ORBassSerre.IsTree` : connected + no non-trivial reduced closed path
-/
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.Subquiver
import Mathlib.Combinatorics.Quiver.ConnectedComponent
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Order.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Set.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v w

namespace Quiver

namespace Path

variable {V : Type u} [Quiver V]
variable {a b c : V}

section HasReverse

variable [Quiver.HasReverse V]

/-- `DeleteBacktrack p q` means that `q` is obtained from `p` by deleting one backtrack,
i.e. one occurrence of two consecutive mutually inverse arrows. -/
inductive DeleteBacktrack : ∀ {a b : V}, Path a b → Path a b → Prop
  | intro {a x y b : V} (p₁ : Path a x) (e : x ⟶ y) (p₂ : Path x b) :
      DeleteBacktrack (p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂)))
        (p₁.comp p₂)


theorem DeleteBacktrack.length_add_two_le {p q : Path a b} (h : DeleteBacktrack p q) :
    q.length + 2 ≤ p.length := by
  cases h with
  | intro p₁ e p₂ =>
    simp only [Path.length_comp, Path.length_toPath]
    omega

theorem DeleteBacktrack.length_lt {p q : Path a b} (h : DeleteBacktrack p q) :
    q.length < p.length := by
  have := h.length_add_two_le
  omega

theorem DeleteBacktrack.comp_right {p q : Path a b} (h : DeleteBacktrack p q) (r : Path b c) :
    DeleteBacktrack (p.comp r) (q.comp r) := by
  cases h with
  | intro p₁ e p₂ =>
    simpa only [Path.comp_assoc] using DeleteBacktrack.intro p₁ e (p₂.comp r)

theorem DeleteBacktrack.comp_left {p q : Path b c} (h : DeleteBacktrack p q) (r : Path a b) :
    DeleteBacktrack (r.comp p) (r.comp q) := by
  cases h with
  | intro p₁ e p₂ =>
    simpa only [Path.comp_assoc] using DeleteBacktrack.intro (r.comp p₁) e p₂

/-- `p.ReducesTo q` means that `q` is obtained from `p` by repeatedly deleting backtracks. -/
def ReducesTo (p q : Path a b) : Prop := Relation.ReflTransGen DeleteBacktrack p q

theorem ReducesTo.refl (p : Path a b) : p.ReducesTo p := Relation.ReflTransGen.refl

theorem ReducesTo.tail {p q : Path a b} (h : p.ReducesTo q) {r : Path a b}
    (hqr : DeleteBacktrack q r) : p.ReducesTo r := Relation.ReflTransGen.tail h hqr

theorem ReducesTo.trans {p q r : Path a b} (h : p.ReducesTo q) (h' : q.ReducesTo r) :
    p.ReducesTo r := Relation.ReflTransGen.trans h h'

theorem ReducesTo.length_le {p q : Path a b} (h : p.ReducesTo q) : q.length ≤ p.length := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hstep ih => exact Nat.le_trans (Nat.le_of_lt hstep.length_lt) ih

theorem ReducesTo.comp_right {p q : Path a b} (h : p.ReducesTo q) (r : Path b c) :
    (p.comp r).ReducesTo (q.comp r) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (hstep.comp_right r)

/-- A path is reduced when no backtrack can be deleted from it. -/
def IsReduced (p : Path a b) : Prop := ∀ q : Path a b, ¬ DeleteBacktrack p q

theorem IsReduced.nil (a : V) : IsReduced (Path.nil : Path a a) := by
  intro q h
  have := h.length_lt
  simp at this

/-- Paths of length at most one are reduced. -/
theorem IsReduced.of_length_lt_two {p : Path a b} (h : p.length < 2) : IsReduced p := by
  intro q hq
  have := hq.length_add_two_le
  omega

theorem IsReduced.of_comp {p : Path a b} {q : Path b c} (h : (p.comp q).IsReduced) :
    p.IsReduced :=
  fun r hr => h _ (hr.comp_right q)

end HasReverse

section HasInvolutiveReverse

variable [Quiver.HasInvolutiveReverse V]

theorem DeleteBacktrack.reverse {p q : Path a b} (h : DeleteBacktrack p q) :
    DeleteBacktrack p.reverse q.reverse := by
  cases h with
  | intro p₁ e p₂ =>
    have h2 : (p₁.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₂))).reverse
        = p₂.reverse.comp (e.toPath.comp ((Quiver.reverse e).toPath.comp p₁.reverse)) := by
      simp only [Path.reverse_comp, Path.reverse_toPath, Quiver.reverse_reverse, Path.comp_assoc]
    rw [h2, Path.reverse_comp]
    exact DeleteBacktrack.intro p₂.reverse e p₁.reverse

theorem ReducesTo.reverse {p q : Path a b} (h : p.ReducesTo q) : p.reverse.ReducesTo q.reverse := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih hstep.reverse

theorem IsReduced.reverse {p : Path a b} (h : p.IsReduced) : p.reverse.IsReduced :=
  fun q hq => h q.reverse (by simpa using hq.reverse)

end HasInvolutiveReverse

section Nil

variable [Quiver.HasReverse V]

theorem qpath_comp_eq_nil_iff {p : Path a a} {q : Path a a} :
    p.comp q = Path.nil ↔ p = Path.nil ∧ q = Path.nil := by
  constructor
  · intro h
    have hlen : p.length + q.length = 0 := by
      have := congrArg Path.length h
      simpa using this
    have hp : p.length = 0 := by omega
    have hq : q.length = 0 := by omega
    exact ⟨eq_nil_of_length_zero _ hp, eq_nil_of_length_zero _ hq⟩
  · rintro ⟨rfl, rfl⟩; rfl

end Nil

end Path

end Quiver

namespace Work.ORBassSerre

open Quiver

variable {V : Type u} [Quiver V]

/-- The induced subgraph on a set `S` of vertices, as a quiver on the subtype. -/
instance quiverSubtype (S : Set V) : Quiver (Set.Elem S) :=
  ⟨fun a b => (a : V) ⟶ (b : V)⟩

instance hasReverseSubtype (S : Set V) [Quiver.HasReverse V] :
    Quiver.HasReverse (Set.Elem S) :=
  ⟨fun {_ _} e => Quiver.reverse (V := V) e⟩

instance hasInvolutiveReverseSubtype (S : Set V) [Quiver.HasInvolutiveReverse V] :
    Quiver.HasInvolutiveReverse (Set.Elem S) :=
  { hasReverseSubtype S with inv' := fun {_ _} e => Quiver.reverse_reverse (V := V) e }

/-- The inclusion of the induced subgraph on a set of vertices into the ambient graph. -/
def subtypePrefunctor (S : Set V) : Set.Elem S ⥤q V where
  obj := Subtype.val
  map := fun e => e

/-- A graph `V` (a quiver with involutive reversal) is a *tree* if it is connected and every
reduced closed path is trivial.  Equivalently: connected and simply connected. -/
def IsTree (V : Type u) [Quiver V] [Quiver.HasInvolutiveReverse V] : Prop :=
  (∀ a b : V, Nonempty (Path a b)) ∧ (∀ a : V, ∀ p : Path a a, p.IsReduced → p = Path.nil)

end Work.ORBassSerre
