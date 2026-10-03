import Mathlib
import Submission.Work.ORHughesFree.Tree

namespace Work.ORHughesFree.Tree

/-! ## Auxiliary facts about `PermRel` and the representative of `0`

`Tree` is the quotient of raw trees `MTree` by `Iso` (equality of the multisets of children,
recursively), and the operations are defined on the representatives picked by `Quotient.out`.
To evaluate `0 * x` we must know that the `Quotient.out` representative of `0` has no children --
which is a statement about the mutual inductive relation `PermRel`. -/

/-- `PermRel`-related lists of children have the same length.

The `Iso` component of the mutual induction is irrelevant here: the only constructor of `PermRel`
that uses it (`cons`) adds one element to each side. -/
theorem zero_mul_permRel_length_eq {l l' : List MTree} (h : PermRel l l') :
    l.length = l'.length :=
  PermRel.rec (motive_1 := fun _ _ _ => True)
    (motive_2 := fun l l' _ => l.length = l'.length)
    (fun _ _ => trivial)
    rfl
    (fun _ _ _ ih2 => by simp [List.length_cons, ih2])
    (fun x y l => rfl)
    (fun l => rfl)
    (fun _ ih => ih.symm)
    (fun _ _ ih1 ih2 => ih1.trans ih2)
    h

/-- The representative of the one-vertex tree `0` provided by `Quotient.out` has no children. -/
theorem zero_mul_children_out_zero : MTree.children (Quotient.out (0 : Tree)) = [] := by
  -- `Quotient.out 0` and `MTree.node []` are related by `Iso`
  have h : Iso (Quotient.out (0 : Tree)) (MTree.node []) := by
    refine @Quotient.exact MTree isoSetoid _ _ ?_
    exact (Quotient.out_eq (0 : Tree)).trans rfl
  -- hence their children are `PermRel`-related; the right-hand list is empty, so the left one has
  -- length zero and is therefore the empty list
  exact List.eq_nil_of_length_eq_zero
    (zero_mul_permRel_length_eq (PermRel.of_iso_children h))

/-- The one-vertex tree is absorbing for `*`: `0 * x = 0`.

Indeed `x * y` is represented by a node whose children are the trees `a + b` for `a` a child of
the `Quotient.out` representative of `x` and `b` one of `y`; for `x = 0` there is no such `a` and
the node has no children, i.e. it is `0` again. -/
theorem zero_mul (x : Tree) : 0 * x = 0 := by
  change Tree.mul (0 : Tree) x = (0 : Tree)
  rw [Tree.mul]
  rw [zero_mul_children_out_zero]
  rfl

end Work.ORHughesFree.Tree
