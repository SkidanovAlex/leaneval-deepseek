/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The *deleted word* of a walk with respect to a set of tree edges

Let `c : α → ℤ` be a weight, `T : Set (α × ℤ)` a set of edges of the level graph (in applications the
tree `winTree Wt c lo hi` of a tree-path gauge) and `w : List (α × Bool)` a word.  The walk of `w`
started at the level `0` is `decor c 0 w`; its edges are `walkEdges c 0 w`.  The **deleted word**
`delWord T c w` is the list of the traversals of `w` whose edge is *not* in `T`, read as letters
`(edge, sign)` of the alphabet `α × ℤ`.

The main result about `delWord` (delegated, see `Submission/Work/OROneRel/delWord_cycred.lean`) is

* `delWord_isCyclicallyReduced`: if `w` is reduced and cyclically reduced with `lsig c w = 0`, and `T`
  is a forest in the sense `ForestUniq` below, then `delWord T c w` is cyclically reduced.

The hypothesis `ForestUniq` is the "unique non-backtracking path" property: two walks with all their
edges in `T`, no immediate backtrack, and the same two endpoints, have the same edge sequence up to
reversal.  For the tree of a tree-path gauge this is what the nestedness invariant of the exploration
supplies.

## Notation

* `WalkIn c T a L` -- the walk of `L` from the level `a` has all its edges in `T`;
* `NoBT c a L` -- the walk has no *immediate backtrack*: no two consecutive traversals use the same
  edge in opposite directions;
* `ForestUniq c T` -- the uniqueness of non-backtracking paths in `T`;
* `walkEdges c a L` -- the list of edges traversed by the walk;
* `delWord T c w` -- the deleted word.
-/
import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.gauge_walk_defs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The list of edges traversed by the walk of `L` started at the level `a`. -/
noncomputable def walkEdges (c : α → ℤ) (a : ℤ) (L : List (α × Bool)) : List (α × ℤ) :=
  (decor c a L).map coverEdge

/-- The walk of `L` from the level `a` runs inside the edge set `T`. -/
def WalkIn (c : α → ℤ) (T : Set (α × ℤ)) (a : ℤ) (L : List (α × Bool)) : Prop :=
  ∀ p ∈ decor c a L, coverEdge p ∈ T

/-- No immediate backtrack: no two consecutive traversals of the walk use the same edge in the two
opposite directions.  (Two traversals of the same edge `e` are in opposite directions exactly when
one starts where the other ends.) -/
def NoBT (c : α → ℤ) (a : ℤ) (L : List (α × Bool)) : Prop :=
  ∀ (L₁ L₂ : List ((α × ℤ) × Bool)) (p q : (α × ℤ) × Bool),
    decor c a L = L₁ ++ p :: q :: L₂ → coverEdge p ≠ coverEdge q ∨ p.2 = q.2

/-- **Uniqueness of non-backtracking paths in the edge set `T`** (the "forest" property).  Two walks
with all edges in `T`, no immediate backtrack, and the same endpoints have the same edge sequence, up
to reversal. -/
def ForestUniq (c : α → ℤ) (T : Set (α × ℤ)) : Prop :=
  ∀ (L₁ L₂ : List (α × Bool)) (a b : ℤ), lsig c L₁ = b - a → WalkIn c T a L₁ → NoBT c a L₁ →
    lsig c L₂ = b - a → WalkIn c T a L₂ → NoBT c a L₂ →
      walkEdges c a L₁ = walkEdges c a L₂ ∨ walkEdges c a L₁ = (walkEdges c a L₂).reverse

/-- The **deleted word** of `L` with respect to the edge set `T`: the traversals of the walk of `L`
from the level `0` whose edge does not lie in `T`, read as letters `(edge, sign)`. -/
noncomputable def delWord (T : Set (α × ℤ)) (c : α → ℤ) (L : List (α × Bool)) :
    List ((α × ℤ) × Bool) := by
  classical
  exact (decor c 0 L).filterMap (fun p => if coverEdge p ∈ T then none else some (coverEdge p, p.2))

end Work.OROneRel
