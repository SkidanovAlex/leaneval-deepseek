import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.Tree.add_comm

/-!
# Associativity of `Tree.add`

`Tree` is the quotient of the raw trees `MTree` by the relation `Iso` (equality of the multisets of
children, recursively).  The addition `x + y` identifies the roots of `x` and `y`; concretely it is
the quotient of `node (children (out x) ++ children (out y))`.

Because `add` is defined on representatives produced by `Quotient.out`, the key point is that it
does not depend on the representative: if `a`, `b` are *any* raw trees isomorphic to `out x`,
`out y` respectively, then

  `x + y = Quotient.mk'' (node (children a ++ children b))`.

Indeed `Iso` of two nodes is exactly `PermRel` of their children lists, and `PermRel` is preserved
by concatenation (this is `PermRel.append_right` / `PermRel.append_left`, proved in
`Submission.Work.ORHughesFree.Tree.add_comm`).  Applying this with `a = out x`-type representatives
of `x + y` and `y + z` turns associativity of `add` into associativity of `List.append`.
-/

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- The raw tree `node (children t)` is isomorphic to `t`; i.e. a tree may be replaced by the node
whose children are its children. -/
theorem add_assoc_iso_out_node (x : Tree) :
    Iso (Quotient.out x) (MTree.node (MTree.children (Quotient.out x))) := by
  cases Quotient.out x with
  | node _ => exact Iso.refl _

/-- `Tree.add` computed on any pair of representatives: if `a` and `b` are raw trees isomorphic to
the chosen representatives of `x` and `y`, then `x + y` is the quotient of `node (a.children ++
b.children)`.  (This is the well-definedness of `add` on the quotient.) -/
theorem add_assoc_add_eq_mk (x y : Tree) (a b : MTree)
    (ha : Iso (Quotient.out x) a) (hb : Iso (Quotient.out y) b) :
    x + y = Quotient.mk'' (MTree.node (MTree.children a ++ MTree.children b)) := by
  show Quotient.mk'' (MTree.node (MTree.children (Quotient.out x) ++
      MTree.children (Quotient.out y))) =
    Quotient.mk'' (MTree.node (MTree.children a ++ MTree.children b))
  refine Quotient.sound (Iso.node ?_)
  exact PermRel.trans
    (PermRel.append_right (PermRel.of_iso_children ha) (MTree.children (Quotient.out y)))
    (PermRel.append_left (PermRel.of_iso_children hb) (MTree.children a))

theorem add_assoc (x y z : Tree) : x + y + z = x + (y + z) := by
  let A := MTree.children (Quotient.out x)
  let B := MTree.children (Quotient.out y)
  let C := MTree.children (Quotient.out z)
  -- `(x + y) + z` computed with the representative `node (A ++ B)` of `x + y`,
  -- which is the defining representative of `x + y`
  have h₂ : (x + y) + z = Quotient.mk'' (MTree.node ((A ++ B) ++ C)) :=
    add_assoc_add_eq_mk (x := x + y) (y := z) (a := MTree.node (A ++ B)) (b := MTree.node C)
      (Quotient.mk_out (MTree.node (A ++ B))) (add_assoc_iso_out_node z)
  -- `x + (y + z)` computed with the representative `node (B ++ C)` of `y + z`
  have h₃ : x + (y + z) = Quotient.mk'' (MTree.node (A ++ (B ++ C))) :=
    add_assoc_add_eq_mk (x := x) (y := y + z) (a := MTree.node A) (b := MTree.node (B ++ C))
      (add_assoc_iso_out_node x) (Quotient.mk_out (MTree.node (B ++ C)))
  rw [h₂, h₃, List.append_assoc]

end Work.ORHughesFree.Tree
