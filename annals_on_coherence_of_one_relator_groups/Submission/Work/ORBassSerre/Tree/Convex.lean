/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convex subsets of trees, and the convex hull

In a tree, a set of vertices is *convex* when it contains, for any two of its points, every
reduced path between those points (equivalently, the unique geodesic).  The induced subgraph on
a convex set is again a tree.

`reducedSpan x y` is the set of vertices lying on a reduced path from `x` to `y`; by uniqueness
of reduced paths in a tree, this is the geodesic segment.  `hull X` is the union of the
`reducedSpan x y` over `x, y ∈ X`, i.e. the convex hull of `X`.
-/
import Submission.Work.ORBassSerre.Tree.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

namespace Work.ORBassSerre

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasReverse V]

/-- The set of vertices lying on a reduced path from `x` to `y`.  In a tree this is the
geodesic segment from `x` to `y`. -/
def reducedSpan (x y : V) : Set V :=
  {v | ∃ p : Quiver.Path x y, p.IsReduced ∧ v ∈ p.vertices}

theorem mem_reducedSpan_iff {x y v : V} :
    v ∈ reducedSpan x y ↔ ∃ p : Quiver.Path x y, p.IsReduced ∧ v ∈ p.vertices := Iff.rfl

theorem self_mem_reducedSpan (x : V) : x ∈ reducedSpan x x :=
  ⟨Quiver.Path.nil, Quiver.Path.IsReduced.nil x, by simp⟩

/-- `S` is convex when every reduced path between two of its vertices stays in `S`. -/
def IsConvexSet (S : Set V) : Prop :=
  ∀ ⦃a : V⦄, a ∈ S → ∀ ⦃b : V⦄, b ∈ S → ∀ p : Quiver.Path a b,
    p.IsReduced → ∀ v ∈ p.vertices, v ∈ S

theorem IsConvexSet.reducedSpan_subset {S : Set V} (hS : IsConvexSet S) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) : reducedSpan a b ⊆ S := by
  rintro v ⟨p, hp, hv⟩
  exact hS ha hb p hp v hv

theorem isConvexSet_univ : IsConvexSet (Set.univ : Set V) := fun _ _ _ _ _ _ _ _ => trivial

theorem IsConvexSet.inter {S T : Set V} (hS : IsConvexSet S) (hT : IsConvexSet T) :
    IsConvexSet (S ∩ T) := by
  intro a ha b hb p hp v hv
  exact ⟨hS ha.1 hb.1 p hp v hv, hT ha.2 hb.2 p hp v hv⟩

/-- The convex hull of a set of vertices: the union of the reduced spans between pairs of
points of the set. -/
def hull (X : Set V) : Set V :=
  {v | ∃ x ∈ X, ∃ y ∈ X, v ∈ reducedSpan x y}

theorem subset_hull (X : Set V) : X ⊆ hull X :=
  fun x hx => ⟨x, hx, x, hx, self_mem_reducedSpan x⟩

theorem hull_mono {X Y : Set V} (h : X ⊆ Y) : hull X ⊆ hull Y :=
  fun _ ⟨x, hx, y, hy, hv⟩ => ⟨x, h hx, y, h hy, hv⟩

end Work.ORBassSerre
