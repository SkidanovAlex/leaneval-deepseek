import Mathlib
import Submission.Work.ORHughesFree.Tree

/-!
# Helper lemmas about `PermRel`, and commutativity of `Tree.add`

`Tree` is the quotient of raw trees `MTree` by the isomorphism relation `Iso`, whose constructor
compares the children of a node by `PermRel` (equality of multisets of pairwise isomorphic trees,
stated as an inductive relation on lists).  Consequently, any statement of the form
`Quotient.mk'' (MTree.node l) = Quotient.mk'' (MTree.node l')` reduces to a `PermRel l l'`
statement about lists.

Here we establish that `PermRel` is invariant under appending on either side, and deduce that
`PermRel (l ++ l') (l' ++ l)`.  This gives `Tree.add_comm`, since `x + y` and `y + x` are the
quotients of `node (children x ++ children y)` and `node (children y ++ children x)`.
-/

namespace Work.ORHughesFree

namespace PermRel

/-- `PermRel` is invariant under appending a fixed list on the right. -/
theorem append_right {l l' : List MTree} (h : PermRel l l') (m : List MTree) :
    PermRel (l ++ m) (l' ++ m) :=
  PermRel.rec (motive_1 := fun _ _ _ => True)
    (motive_2 := fun l l' _ => PermRel (l ++ m) (l' ++ m))
    (fun _ _ => trivial)
    (PermRel.refl m)
    (fun hx _ _ ih => PermRel.cons hx ih)
    (fun x y l => PermRel.swap x y (l ++ m))
    (fun l => PermRel.refl (l ++ m))
    (fun _ ih => PermRel.symm ih)
    (fun _ _ ih1 ih2 => PermRel.trans ih1 ih2)
    h

/-- `PermRel` is invariant under appending a fixed list on the left. -/
theorem append_left {l l' : List MTree} (h : PermRel l l') (m : List MTree) :
    PermRel (m ++ l) (m ++ l') := by
  induction m with
  | nil => exact h
  | cons a m ih => exact PermRel.cons (Iso.refl a) ih

/-- A single element can be rotated from the head of a list to its tail. -/
theorem rotate (a : MTree) (l : List MTree) : PermRel (a :: l) (l ++ [a]) := by
  induction l with
  | nil => exact PermRel.refl [a]
  | cons b l ih =>
    exact PermRel.trans (PermRel.swap a b l) (PermRel.cons (Iso.refl b) ih)

/-- Two lists can be swapped around the concatenation. -/
theorem append_comm (l1 l2 : List MTree) : PermRel (l1 ++ l2) (l2 ++ l1) := by
  induction l1 with
  | nil => simpa using PermRel.refl l2
  | cons a l1 ih =>
    have h1 : PermRel (a :: (l1 ++ l2)) ((l1 ++ l2) ++ [a]) := rotate a (l1 ++ l2)
    have h2 : PermRel ((l1 ++ l2) ++ [a]) ((l2 ++ l1) ++ [a]) := append_right ih [a]
    have h3 : PermRel ((l2 ++ l1) ++ [a]) (l2 ++ (a :: l1)) := by
      rw [List.append_assoc]
      exact append_left (PermRel.symm (rotate a l1)) l2
    exact PermRel.trans (PermRel.trans h1 h2) h3

end PermRel

end Work.ORHughesFree

namespace Work.ORHughesFree.Tree

theorem add_comm (x y : Tree) : x + y = y + x := by
  apply Quotient.sound
  exact Iso.node (PermRel.append_comm (MTree.children (Quotient.out x))
    (MTree.children (Quotient.out y)))

end Work.ORHughesFree.Tree
