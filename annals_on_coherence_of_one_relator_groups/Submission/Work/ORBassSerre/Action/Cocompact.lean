/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cocompact invariant subtrees

A finitely generated group acting on a tree has a cocompact invariant subtree (a *minimal
subtree* containing a point and its translates by a finite generating set).  This is the standard
"finitely generated ⟹ cocompact" step used in Bass--Serre theory.

## Main results

* `Work.ORBassSerre.exists_invariant_cocompact_subtree`
-/
import Submission.Work.ORBassSerre.Action.Quotient
import Submission.Work.ORBassSerre.Tree.Convex
import Mathlib.GroupTheory.Finiteness

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v w

namespace Work.ORBassSerre

open Quiver

variable {G : Type u} {V : Type v} [Group G] [Quiver V] [Quiver.HasReverse V] [MulAction G V]
  [GraphAction G V]

/-- A set of vertices is invariant under a subgroup `H` of `G`. -/
def IsInvariantUnder (H : Subgroup G) (S : Set V) : Prop :=
  ∀ ⦃h : G⦄, h ∈ H → ∀ ⦃v : V⦄, v ∈ S → h • v ∈ S

/-- A `G`-action on a graph is *without inversions* if no group element reverses an edge. -/
def ActsWithoutInversions (G : Type u) (V : Type v) [Group G] [Quiver V] [Quiver.HasReverse V]
    [MulAction G V] [GraphAction G V] : Prop :=
  ∀ (g : G) (e : Quiver.Total V), GraphAction.smulTotal g e ≠ e.reverse

/-- The `H`-orbits on a set `S` of vertices are finite, expressed through a finite fundamental
domain. -/
def HasFinitelyManyOrbits (H : Subgroup G) (S : Set V) : Prop :=
  ∃ T : Finset V, ∀ v ∈ S, ∃ h : G, h ∈ H ∧ ∃ t ∈ T, h • t = v

/-- The `H`-orbits on the edges of the induced subgraph on `S` are finite, expressed through a
finite fundamental domain of edges. -/
def HasFinitelyManyEdgeOrbits (H : Subgroup G) (S : Set V) : Prop :=
  ∃ F : Finset (Quiver.Total V), ∀ e : Quiver.Total V, e.left ∈ S → e.right ∈ S →
    ∃ h : G, h ∈ H ∧ ∃ f ∈ F, h • f = e

theorem isInvariantUnder_iff {H : Subgroup G} {S : Set V} :
    IsInvariantUnder H S ↔ ∀ h : H, ∀ v ∈ S, (h : G) • v ∈ S := by
  constructor
  · intro hS h v hv
    exact hS h.2 hv
  · intro hS g hg v hv
    exact hS ⟨g, hg⟩ v hv

theorem IsInvariantUnder.union {H : Subgroup G} {S : Set V} {ι : Type*}
    (A : ι → Set V) (h : ∀ i, IsInvariantUnder H (A i)) : IsInvariantUnder H (⋃ i, A i) := by
  intro g hg v hv
  simp only [Set.mem_iUnion] at hv ⊢
  obtain ⟨i, hvi⟩ := hv
  exact ⟨i, h i (h := g) hg hvi⟩

end Work.ORBassSerre
