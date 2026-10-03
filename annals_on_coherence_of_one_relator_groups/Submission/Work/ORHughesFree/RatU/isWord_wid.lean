/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Words of `Rat(U)` have width one

[JZLA20, Lemma 4.3(xiii)]: the elements of the `U`-biset `U ♮ X` of words of [JZLA20, §4.2]
have complexity of width one, i.e. `Tree α` is a single root extension.  This is the fact that
makes the "equality" case of the complexity induction of [JZLA20, Proposition 5.1] produce a
single coefficient.

In the term model `RatU U` of `Submission/Work/ORHughesFree/Rat/RTerm.lean` a word is generated
by the images `ofGroup u` of the group elements, by products, and by the `⋄` of an arbitrary
element (`RatU.IsWord`, `Submission/Work/ORHughesFree/Rat/Word.lean`), so the statement follows
by induction on the generation, using additivity and multiplicativity of the width
(`Submission/Work/ORHughesFree/Tree/Log.lean`):

* `Tree (ofGroup u) = 1` and `wid 1 = 1`;
* `wid (x * y) = wid x * wid y`;
* `Tree (x⋄) = exp (exp (Tree x))` and `wid (exp z) = 1`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Rat.Word

namespace Work.ORHughesFree.RatU

open Work.ORHughesFree

/-- The one-edge tree has width one; this is `Tree.wid_exp` at the one-vertex tree, written for
the numeral `1 : Tree` (which is definitionally `Tree.exp 0`). -/
theorem wid_one : Work.ORHughesFree.Tree.wid (1 : Work.ORHughesFree.Tree) = 1 :=
  Work.ORHughesFree.Tree.wid_exp 0

/-- **[JZLA20, Lemma 4.3(xiii)]**: a word of `Rat(U)` has complexity of width `1`. -/
theorem isWord_wid {U : Type} [Group U] {x : Work.ORHughesFree.RatU U}
    (h : Work.ORHughesFree.RatU.IsWord x) :
    Work.ORHughesFree.Tree.wid (Work.ORHughesFree.Rat.treeOfRat U x) = 1 := by
  induction h with
  | ofGroup u =>
      rw [Work.ORHughesFree.Rat.treeOfRat_ofGroup]
      exact wid_one
  | mul hx hy ihx ihy =>
      rw [Work.ORHughesFree.Rat.treeOfRat_mul, Work.ORHughesFree.Tree.wid_mul, ihx, ihy, mul_one]
  | rat y hy =>
      rw [Work.ORHughesFree.Rat.treeOfRat_rat_rational hy, Work.ORHughesFree.Tree.wid_exp]

end Work.ORHughesFree.RatU
