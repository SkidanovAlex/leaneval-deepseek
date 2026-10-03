import Mathlib
import Submission.Work.ORHughesFree.Tree.order_defs
import Submission.Work.ORHughesFree.Tree.fam_mul

/-!
# Strict order is invariant under adding a common tree on the right

The well-order `lt` on finite rooted trees (`Submission/Work/ORHughesFree/Tree/order_defs.lean`)
is defined recursively through the Dershowitz–Manna ordering of the families of children.  This
file records the elementary compatibility of `lt` with the monoid operation `+`: adding the same
tree `c` on the right of both sides of `a < b` preserves the strict order.

The proof is a direct computation with the unfolding `lt_iff`.  From `fam a X + Y` and
`fam b = X + Z` (with `Z ≠ 0`, and every element of `Y` strictly below some element of `Z`) we
conclude the same Dershowitz–Manna decomposition for `fam (a + c)` and `fam (b + c)`, using the
key identity `fam (x + y) = fam x + fam y` relating `+` on trees to the union of families.
-/

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- The family of a sum is the sum (union) of the families: `fam (x + y) = fam x + fam y`.
This is the bridge between addition of trees and addition of multisets of subtrees. -/
private theorem fam_add (x y : Tree) : fam (x + y) = fam x + fam y := by
  change fam (mkT (MTree.node (MTree.children (Quotient.out x) ++
    MTree.children (Quotient.out y)))) = fam x + fam y
  rw [fam_mkT]
  simp only [MTree.children]
  rw [List.map_append, ← Multiset.coe_add]
  rfl

/-- **Adding a tree on the right preserves the strict order.**  If `a < b` then `a + c < b + c`.
Concretely, the Dershowitz–Manna decomposition of `fam b` over `fam a` is unaffected by adjoining
the common family `fam c` to both sides. -/
theorem lt_add_right {a b : Tree} (h : lt a b) (c : Tree) : lt (a + c) (b + c) := by
  rw [lt_iff] at h
  obtain ⟨X, Y, Z, hZ, h1, h2, h3⟩ := h
  rw [lt_iff]
  refine ⟨X + fam c, Y, Z, hZ, ?_, ?_, h3⟩
  · rw [fam_add, h1]; ac_rfl
  · rw [fam_add, h2]; ac_rfl

end Work.ORHughesFree.Tree
