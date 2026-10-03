/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The product formula for the finite rooted trees

`Tree` is the type of finite rooted trees up to isomorphism, i.e. the initial algebra of the
multiset functor `X ↦ Multiset X` (`Submission/Work/ORHughesFree/Tree.lean`), with

* `x + y` identifying the roots of `x` and `y` (`fam (x + y) = fam x + fam y`),
* `x * y = ∑_{a ∈ fam x, b ∈ fam y} exp (a + b)` as in [JZLA20, §4.1],
* `exp x` the tree with the single child `x`, so that `fam (exp x) = {x}`,
* `fam x` the multiset of children of `x` (`Submission/Work/ORHughesFree/Tree/fam_mul.lean`).

This file proves the recursion of [JZLA20, §4.1] for the multiplication, i.e. the product formula
`x * y = ∑_{a ∈ fam x} ∑_{b ∈ fam y} exp (a + b)`.

Two occurrences of `Multiset`, in the product `∑_{a ∈ fam x, b ∈ fam y}` and in the sum of trees,
have to be reconciled.  The bridge is the reconstruction identity
`((fam x).map exp).sum = x` (`Tree.sum_fam`): a tree is the sum of the one-child trees over its
family.  Applying it to `x * y` and rewriting `fam (x * y)` by the recursion
`fam (x * y) = (fam x).bind (fun a => (fam y).map (fun b => a + b))` (`Tree.fam_mul`), it remains
to push the `map exp` through the `bind`, which is the `Multiset` identity
`Multiset.map_bind` followed by `Multiset.map_map`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.TreeInstances
import Submission.Work.ORHughesFree.Tree.exp_add
import Submission.Work.ORHughesFree.Tree.fam_exp
import Submission.Work.ORHughesFree.Tree.fam_mul
import Submission.Work.ORHughesFree.Tree.sum_fam

set_option autoImplicit false

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- The family of a product, with the summands already pushed through `exp`:
`fam (x * y) = {exp (a + b) : a ∈ fam x, b ∈ fam y}` read as a multiset of one-child trees.  This
is `Tree.fam_mul` with `exp` pushed inside using `fam (exp c) = {c}`, the multiset form of the
fact that summing `exp` over a family reconstructs the tree. -/
theorem map_exp_fam_mul (x y : Tree) :
    (fam (x * y)).map exp =
      (fam x).bind (fun a => (fam y).map (fun b => exp (a + b))) := by
  rw [fam_mul, Multiset.map_bind]
  refine Multiset.bind_congr (fun a _ => ?_)
  rw [Multiset.map_map]
  rfl

/-- **The product formula of [JZLA20, §4.1]**: the product of two finite rooted trees is the sum
of the one-child trees `exp (a + b)` over the children `a` of `x` and the children `b` of `y`.

Indeed both sides are trees with the same family (`map_exp_fam_mul`), and a tree is determined by
its family; equivalently, `Tree.sum_fam` reconstructs a tree from its family of one-child trees, and
`fam_mul` computes the family of the product. -/
theorem mul_eq (x y : Tree) :
    x * y = (((fam x).bind (fun a => (fam y).map (fun b => exp (a + b))))).sum := by
  have h : ((fam (x * y)).map exp).sum =
      (((fam x).bind (fun a => (fam y).map (fun b => exp (a + b))))).sum :=
    congrArg Multiset.sum (map_exp_fam_mul x y)
  exact (sum_fam (x * y)).symm.trans h

end Work.ORHughesFree.Tree
