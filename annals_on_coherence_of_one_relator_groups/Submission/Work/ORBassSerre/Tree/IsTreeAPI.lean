/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The API of a tree

Consequences of `Work.ORBassSerre.IsTree`: the unique geodesic (reduced path) between two
vertices, and its basic properties.
-/
import Submission.Work.ORBassSerre.Tree.Basic
import Submission.Work.ORBassSerre.Tree.Convex
import Submission.Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_exists_isReduced
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_vertices_subset_of_reducesTo

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

namespace Work.ORBassSerre

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

theorem IsTree.exists_isReduced (h : IsTree V) (a b : V) :
    ∃ p : Quiver.Path a b, p.IsReduced :=
  Tree.Reduction.qpath_exists_isReduced (h.1 a b)

theorem IsTree.subsingleton_isReduced (h : IsTree V) (a b : V) :
    Subsingleton {p : Quiver.Path a b // p.IsReduced} :=
  ⟨fun p q => Subtype.ext (Tree.Geodesic.qpath_eq_of_isTree h p.2 q.2)⟩

/-- The unique reduced path (geodesic) from `a` to `b` in a tree. -/
noncomputable def IsTree.geodesic (h : IsTree V) (a b : V) : Quiver.Path a b :=
  Classical.choose (h.exists_isReduced a b)

theorem IsTree.geodesic_isReduced (h : IsTree V) (a b : V) : (h.geodesic a b).IsReduced :=
  Classical.choose_spec (h.exists_isReduced a b)

/-- Any reduced path from `a` to `b` is the geodesic. -/
theorem IsTree.eq_geodesic (h : IsTree V) {a b : V} {p : Quiver.Path a b}
    (hp : p.IsReduced) : p = h.geodesic a b :=
  Tree.Geodesic.qpath_eq_of_isTree h hp (h.geodesic_isReduced a b)

theorem IsTree.geodesic_self (h : IsTree V) (a : V) :
    h.geodesic a a = Quiver.Path.nil :=
  (h.eq_geodesic (Quiver.Path.IsReduced.nil a)).symm

theorem IsTree.start_mem_geodesic (h : IsTree V) (a b : V) :
    a ∈ (h.geodesic a b).vertices :=
  Quiver.Path.start_mem_vertices _

theorem IsTree.end_mem_geodesic (h : IsTree V) (a b : V) :
    b ∈ (h.geodesic a b).vertices :=
  Quiver.Path.end_mem_vertices _

theorem IsTree.reducedSpan_eq (h : IsTree V) (a b : V) :
    reducedSpan a b = {v | v ∈ (h.geodesic a b).vertices} := by
  ext v
  constructor
  · rintro ⟨p, hp, hv⟩
    rw [h.eq_geodesic hp] at hv
    exact hv
  · intro hv
    exact ⟨h.geodesic a b, h.geodesic_isReduced a b, hv⟩

end Work.ORBassSerre
