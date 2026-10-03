import Mathlib
import Submission.Work.ORHughesFree.Tree

namespace Work.ORHughesFree

namespace MTree

/-- Rebuilding a raw tree from its list of children returns the tree itself. -/
private theorem node_children (t : MTree) : MTree.node (MTree.children t) = t := by
  cases t; rfl

end MTree

namespace Tree

/-- `PermRel` preserves the length of a list. -/
private theorem PermRel.length_eq : ∀ {l l' : List MTree}, PermRel l l' → l.length = l'.length := by
  intro l l' h
  induction h using PermRel.rec (motive_1 := fun _ _ _ => True) with
  | node a ih => trivial
  | nil => rfl
  | cons a a' ih1 ih2 => simp [ih2]
  | swap x y l => simp
  | refl l => rfl
  | symm a ih => exact ih.symm
  | trans a a' ih1 ih2 => exact ih1.trans ih2

/-- A list `PermRel`-equivalent to the empty list is empty. -/
private theorem PermRel.eq_nil {l : List MTree} (h : PermRel l []) : l = [] := by
  have hh := PermRel.length_eq h
  simpa using hh

/-- `0` is the one-vertex tree, so adding it to `x` identifies no new subtree:
`0`'s representative has no children, and `x`'s representative is recovered from its own children. -/
theorem zero_add (x : Tree) : 0 + x = x := by
  have h0 : MTree.children (Quotient.out (0 : Tree)) = [] :=
    PermRel.eq_nil (PermRel.of_iso_children (Quotient.exact (Quotient.out_eq (0 : Tree))))
  have key : (Quotient.mk'' (MTree.node (MTree.children (Quotient.out (0 : Tree)) ++
      MTree.children (Quotient.out x))) : Tree) = Quotient.mk'' (Quotient.out x) := by
    apply Quotient.sound
    have h1 : PermRel (MTree.children (Quotient.out (0 : Tree)) ++ MTree.children (Quotient.out x))
        (MTree.children (Quotient.out x)) := by
      rw [h0]
      exact PermRel.refl _
    have h2 : Iso (MTree.node (MTree.children (Quotient.out x))) (Quotient.out x) := by
      rw [MTree.node_children]
      exact Iso.refl _
    exact Iso.trans (Iso.node h1) h2
  exact (show (0 : Tree) + x = (Quotient.mk'' (MTree.node (MTree.children (Quotient.out (0 : Tree)) ++
      MTree.children (Quotient.out x))) : Tree) from rfl).trans (key.trans (Quotient.out_eq x))

end Tree

end Work.ORHughesFree
