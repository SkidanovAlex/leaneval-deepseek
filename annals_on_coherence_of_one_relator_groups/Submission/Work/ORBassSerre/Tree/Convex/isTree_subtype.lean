import Mathlib
import Submission.Work.ORBassSerre.Tree.Convex
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Subgraph.qpath_exists_restrict
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced

namespace Work.ORBassSerre.Tree.Convex

universe u

open Quiver

section MapReverse

variable {V : Type u} [Quiver V] [Quiver.HasReverse V]

/-- The inclusion `subtypePrefunctor S` of the induced subgraph on `S` into the ambient graph
preserves reversal of arrows. -/
instance subtypePrefunctor_mapReverse (S : Set V) :
    (Work.ORBassSerre.subtypePrefunctor S).MapReverse where
  map_reverse' _ := rfl

end MapReverse

/-- The induced subgraph on a convex set of vertices of a tree is a tree. -/
theorem isTree_subtype {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (h : Work.ORBassSerre.IsTree V) {S : Set V} (hS : Work.ORBassSerre.IsConvexSet S) :
    Work.ORBassSerre.IsTree (S : Type u) := by
  refine ⟨?_, ?_⟩
  · -- connectivity: restrict a reduced path between the two vertices, using convexity
    intro a b
    obtain ⟨p, hp⟩ := h.exists_isReduced (a : V) (b : V)
    obtain ⟨p', _⟩ := Work.ORBassSerre.Tree.Subgraph.qpath_exists_restrict (S := S) a.2 b.2 p
      (fun v hv => hS a.2 b.2 p hp v hv)
    exact ⟨p'⟩
  · -- acyclicity: push a reduced closed path down to the ambient tree
    intro a p hp
    have hmap : ((Work.ORBassSerre.subtypePrefunctor S).mapPath p).IsReduced :=
      Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced (Work.ORBassSerre.subtypePrefunctor S)
        Subtype.val_injective (fun {_ _} _ _ hxy => hxy) hp
    have hnil : (Work.ORBassSerre.subtypePrefunctor S).mapPath p = Quiver.Path.nil :=
      h.2 (a : V) _ hmap
    cases p with
    | nil => rfl
    | cons p' e =>
      rw [Prefunctor.mapPath_cons] at hnil
      exact absurd hnil (Quiver.Path.cons_ne_nil _ _)

end Work.ORBassSerre.Tree.Convex
