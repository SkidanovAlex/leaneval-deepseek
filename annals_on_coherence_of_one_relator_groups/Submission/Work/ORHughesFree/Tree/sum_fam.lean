import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.TreeInstances
import Submission.Work.ORHughesFree.Tree.fam_exp
import Submission.Work.ORHughesFree.Tree.fam_mul

/-!
# `fam x` sums to `x`

The defining relation between a tree `x` and its family of subtrees `fam x` is that `x` is the
sum of the one-child trees `exp a` over `a ∈ fam x`: adding trees identifies their roots, so
adding `exp a` for every child `a` of `x` rebuilds `x`.

The file `Submission.Work.ORHughesFree.Tree.fam_mul` introduces the auxiliary `mkT` (the
`Quotient.mk''` of `MTree` into `Tree`) together with the compatibility lemma
`add_mkT : mkT a + mkT b = mkT (node (children a ++ children b))`.  We first prove the list-level
statement that summing `exp (mkT c)` over a list of raw trees rebuilds the node on that list (its
children being the `Quotient.out` of the entries, which are `Iso` to the entries), and then read
off the result for `l = children (out x)`.
-/

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- `exp` of `mkT c` is by definition the `mkT` of the node with the single child
`Quotient.out (mkT c)`. -/
private theorem exp_mkT (c : MTree) :
    exp (mkT c) = mkT (MTree.node [Quotient.out (mkT c)]) := rfl

/-- Summing `exp (mkT c)` over the entries of a list `l` rebuilds the node on `l`, with each child
replaced by the representative `Quotient.out (mkT c)` chosen for it. -/
theorem list_sum_map_exp (l : List MTree) :
    (l.map (fun c => exp (mkT c))).sum =
      mkT (MTree.node (l.map (fun c => Quotient.out (mkT c)))) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.map_cons, List.sum_cons, ih, exp_mkT, add_mkT]
    rfl

theorem sum_fam (x : Tree) : ((fam x).map exp).sum = x := by
  -- `fam x` unfolds to the multiset of `mkT c` for the raw children `c` of `out x`.
  have hfam : fam x
      = (((MTree.children (Quotient.out x)).map mkT : List Tree) : Multiset Tree) := rfl
  rw [hfam, Multiset.map_coe, Multiset.sum_coe, List.map_map]
  -- Replace the composed map `exp ∘ mkT` by the explicit lambda of the list lemma.
  show (List.map (fun c => exp (mkT c)) (MTree.children (Quotient.out x))).sum = x
  rw [list_sum_map_exp]
  -- The remaining raw node is isomorphic to `out x`, hence represents `x`.
  have hnode_eq : MTree.node (MTree.children (Quotient.out x)) = Quotient.out x := by
    cases Quotient.out x with
    | node l => rfl
  have hp : PermRel
      ((MTree.children (Quotient.out x)).map (fun c => Quotient.out (mkT c)))
      (MTree.children (Quotient.out x)) := by
    simpa using
      (PermRel.map_congr (f := fun c => Quotient.out (mkT c)) (g := id)
        (fun a => iso_out_mkT a) (MTree.children (Quotient.out x)))
  have hIso : Iso (MTree.node ((MTree.children (Quotient.out x)).map
      (fun c => Quotient.out (mkT c)))) (Quotient.out x) := by
    rw [← hnode_eq]
    exact Iso.node hp
  exact (Quotient.sound hIso).trans (Quotient.out_eq x)

end Work.ORHughesFree.Tree
