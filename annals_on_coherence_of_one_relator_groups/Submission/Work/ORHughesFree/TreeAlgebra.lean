/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The finite rooted trees form a `RootedTreeAlgebra`

Combines the operation lemmas on `Work.ORHughesFree.Tree` into a model of
`RootedTreeAlgebra` ([JZLA20, §4.1]).  The order-theoretic part (`RootedTrees`) is separate.
-/
import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.TreeInstances
import Submission.Work.ORHughesFree.Tree.exp_add
import Submission.Work.ORHughesFree.Tree.fam_exp
import Submission.Work.ORHughesFree.Tree.sum_fam
import Submission.Work.ORHughesFree.Tree.mul_eq
import Submission.Work.ORHughesFree.JZLA20

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

/-- The finite rooted trees of [JZLA20, §4.1] form a model of the algebraic part of the tree
semiring. -/
noncomputable def rootedTreeAlgebra : RootedTreeAlgebra Tree where
  exp := Tree.exp
  exp_zero := rfl
  exp_add := Tree.exp_add
  fam := Tree.fam
  fam_exp := Tree.fam_exp
  sum_fam := Tree.sum_fam
  mul_eq := Tree.mul_eq

/-- The algebraic part of the tree semiring of [JZLA20, §4.1] is inhabited by the concrete trees. -/
theorem exists_rootedTreeAlgebra : Nonempty (RootedTreeAlgebra Tree) :=
  ⟨rootedTreeAlgebra⟩

end Work.ORHughesFree
