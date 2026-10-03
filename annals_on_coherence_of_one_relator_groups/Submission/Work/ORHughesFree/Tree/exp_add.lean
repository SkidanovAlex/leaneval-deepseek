import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.Tree.add_comm
import Submission.Work.ORHughesFree.Tree.permRel_singleton

/-!
# `exp (x + y) = exp x * exp y`

`Tree` is the quotient of the raw finite rooted trees `MTree` by the isomorphism relation `Iso`,
whose children relation is the mutual inductive `PermRel`; `exp x` is the tree whose (single) child
is `x`, i.e. the class of `MTree.node [Quotient.out x]`.  The operations are defined through the
representatives picked by `Quotient.out`:

`x * y = ⟦node ((children (out x)).flatMap (fun a => (children (out y)).map (fun b =>
node (children a ++ children b))))⟧`.

`Quotient.out (exp x)` is a representative of `node [Quotient.out x]`, so its list of children is
`PermRel`-equivalent to the singleton `[Quotient.out x]`, and by
`Submission.Work.ORHughesFree.Tree.permRel_singleton` it *is* a singleton `[a]` with
`Iso a (Quotient.out x)`.  Substituting these two singletons collapses the double sum defining
`exp x * exp y` to the single summand `node (children a ++ children b)`, which represents `x + y`;
the resulting class is exactly the defining representative of `exp (x + y)`.

Equivalently, in the language of [JZLA20, §4.1], `fam (exp x) = {x}` is the statement that a
single-child tree has exactly one subtree, so both sides of the identity have the same family.
-/

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

theorem exp_add (x y : Tree) : exp (x + y) = exp x * exp y := by
  -- The representatives of `exp x` and `exp y` are single-child nodes.
  have hx : Iso (Quotient.out (exp x)) (MTree.node [Quotient.out x]) :=
    @Quotient.exact MTree isoSetoid _ _ ((Quotient.out_eq (exp x)).trans rfl)
  have hy : Iso (Quotient.out (exp y)) (MTree.node [Quotient.out y]) :=
    @Quotient.exact MTree isoSetoid _ _ ((Quotient.out_eq (exp y)).trans rfl)
  -- Hence they have a single child, isomorphic to `Quotient.out x` resp. `Quotient.out y`.
  obtain ⟨a, ha, ha_iso⟩ := permRel_singleton (PermRel.of_iso_children hx)
  obtain ⟨b, hb, hb_iso⟩ := permRel_singleton (PermRel.of_iso_children hy)
  -- Unfolding the definition of the product on these representatives.
  have hmul : exp x * exp y = Quotient.mk'' (MTree.node
      ((MTree.children (Quotient.out (exp x))).flatMap (fun a' =>
        (MTree.children (Quotient.out (exp y))).map (fun b' =>
          MTree.node (MTree.children a' ++ MTree.children b'))))) := rfl
  -- The double sum therefore collapses to the single summand `node (children a ++ children b)`.
  have hchildren : (MTree.children (Quotient.out (exp x))).flatMap (fun a' =>
        (MTree.children (Quotient.out (exp y))).map (fun b' =>
          MTree.node (MTree.children a' ++ MTree.children b')))
      = [MTree.node (MTree.children a ++ MTree.children b)] := by
    rw [ha, hb]
    simp
  -- That summand represents `x + y`.
  have hrep : (Quotient.mk'' (MTree.node (MTree.children a ++ MTree.children b)) : Tree) =
      x + y := by
    show (Quotient.mk'' (MTree.node (MTree.children a ++ MTree.children b)) : Tree) =
      Quotient.mk'' (MTree.node (MTree.children (Quotient.out x) ++
        MTree.children (Quotient.out y)))
    exact Quotient.sound (Iso.node (PermRel.trans
      (PermRel.append_right (PermRel.of_iso_children ha_iso) (MTree.children b))
      (PermRel.append_left (PermRel.of_iso_children hb_iso) (MTree.children (Quotient.out x)))))
  have hiso : Iso (MTree.node (MTree.children a ++ MTree.children b)) (Quotient.out (x + y)) :=
    @Quotient.exact MTree isoSetoid _ _ (hrep.trans (Quotient.out_eq (x + y)).symm)
  rw [hmul, hchildren]
  exact (Quotient.sound (Iso.node (PermRel.cons hiso (PermRel.refl [])))).symm

end Work.ORHughesFree.Tree
