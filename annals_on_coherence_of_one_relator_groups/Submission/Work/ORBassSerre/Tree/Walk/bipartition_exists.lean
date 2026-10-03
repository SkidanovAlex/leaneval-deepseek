import Mathlib
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced

/-!
# Trees are bipartite

A graph in this development is a `Quiver` with an involutive reversal of arrows, and
`Work.ORBassSerre.IsTree V` says that it is connected and that every reduced closed path is
trivial (`Submission/Work/ORBassSerre/Tree/Basic.lean`).

The target of this file is `Work.ORBassSerre.Tree.Walk.bipartition_exists`: a tree has a
2-colouring of its vertices such that the two ends of every arrow have different colours.

The colouring is by the parity of the length of the (unique) geodesic from a fixed base vertex.
The mathematical content is that this parity is well defined: any path between two vertices can
be reduced, by deleting backtracks, to the geodesic, and deleting a backtrack removes exactly
two arrows and hence preserves the parity of the length.

## Main results

* `Quiver.Path.DeleteBacktrack.length_eq_add_two` : deleting a backtrack removes exactly two
  arrows (the companion of `Quiver.Path.DeleteBacktrack.length_add_two_le`).
* `Quiver.Path.ReducesTo.length_mod_two` : reduction preserves the parity of the length.
* `IsTree.path_length_mod_two` : in a tree all paths between two vertices have the same parity
  of length, namely that of the geodesic.
* `Work.ORBassSerre.Tree.Walk.bipartition_exists` : a tree is bipartite.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace Quiver

namespace Path

variable {V : Type u} [Quiver V] [Quiver.HasReverse V]
variable {a b : V}

/-- Deleting a backtrack removes exactly two arrows from a path: the two arrows of the backtrack
itself.  This strengthens `Quiver.Path.DeleteBacktrack.length_add_two_le` to an equality. -/
theorem DeleteBacktrack.length_eq_add_two {p q : Path a b} (h : DeleteBacktrack p q) :
    p.length = q.length + 2 := by
  cases h with
  | intro p₁ e p₂ =>
    simp only [Path.length_comp, Path.length_toPath]
    omega

/-- Deleting backtracks preserves the parity of the length of a path. -/
theorem ReducesTo.length_mod_two {p q : Path a b} (h : p.ReducesTo q) :
    p.length % 2 = q.length % 2 := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    have hlen := hstep.length_eq_add_two
    omega

end Path

end Quiver

namespace Work.ORBassSerre

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- In a tree, the parity of the length of a path between two vertices depends only on the
endpoints: it is the parity of the length of the (unique) geodesic.

Indeed, the path reduces to a reduced path with the same endpoints, which is the geodesic by
uniqueness of reduced paths, and reduction preserves parity
(`Quiver.Path.ReducesTo.length_mod_two`). -/
theorem IsTree.path_length_mod_two (h : IsTree V) {a b : V} (p : Quiver.Path a b) :
    p.length % 2 = (h.geodesic a b).length % 2 := by
  obtain ⟨q, hr, hred⟩ := Tree.Reduction.qpath_exists_reducesTo_isReduced p
  have hq : q = h.geodesic a b := h.eq_geodesic hred
  rw [← hq]
  exact hr.length_mod_two

end Work.ORBassSerre

namespace Work.ORBassSerre.Tree.Walk

open Quiver

/-- Two natural numbers have parities of opposite `Bool`-colourings: if `n % 2 ≠ m % 2` then the
`Bool` values `n % 2 == 1` and `m % 2 == 1` differ. -/
theorem bool_ne_of_mod_two_ne {n m : ℕ} (h : n % 2 ≠ m % 2) :
    (n % 2 == 1) ≠ (m % 2 == 1) := by
  intro hh
  apply h
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    simp_all

/-- **A tree is bipartite.**  For a tree `V` there is a `Bool`-valued colouring of the vertices
such that the two ends of every arrow carry different colours.

Choose a base vertex `a₀` and colour a vertex `v` by the parity of the length of the geodesic
from `a₀` to `v`.  If `e : u ⟶ v` is an arrow, then the path `geodesic a₀ u · e` from `a₀` to
`v` has length one more than `geodesic a₀ u`, so by `IsTree.path_length_mod_two` the parity of
`geodesic a₀ v` is opposite to that of `geodesic a₀ u`.  (In particular such an arrow can never
join a vertex to itself, which is why the parity argument always gives a genuine inequality.) -/
theorem bipartition_exists {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (hT : Work.ORBassSerre.IsTree V) :
    ∃ c : V → Bool, ∀ e : Quiver.Total V, c e.left ≠ c e.right := by
  by_cases hV : Nonempty V
  · obtain ⟨a₀⟩ := hV
    refine ⟨fun v => ((hT.geodesic a₀ v).length % 2 == 1), ?_⟩
    intro e
    apply bool_ne_of_mod_two_ne
    have hp : ((hT.geodesic a₀ e.left).comp e.hom.toPath).length
        = (hT.geodesic a₀ e.left).length + 1 := by
      rw [Quiver.Path.length_comp, Quiver.Path.length_toPath]
    have hpar := IsTree.path_length_mod_two hT
      ((hT.geodesic a₀ e.left).comp e.hom.toPath)
    intro hcontra
    omega
  · -- An empty tree has no arrows, so any colouring works.
    refine ⟨fun v => (hV ⟨v⟩).elim, ?_⟩
    intro e
    exact (hV ⟨e.left⟩).elim

end Work.ORBassSerre.Tree.Walk
