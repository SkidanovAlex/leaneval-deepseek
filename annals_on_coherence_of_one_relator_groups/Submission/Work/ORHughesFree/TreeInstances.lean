/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The commutative monoid structures on the trees

Assembles the operation lemmas proved in `Submission/Work/ORHughesFree/Tree/` into the `AddCommMonoid`,
`CommMonoid` and `Distrib` instances on `Work.ORHughesFree.Tree`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.Tree.add_comm
import Submission.Work.ORHughesFree.Tree.add_assoc
import Submission.Work.ORHughesFree.Tree.zero_add
import Submission.Work.ORHughesFree.Tree.add_zero
import Submission.Work.ORHughesFree.Tree.mul_comm
import Submission.Work.ORHughesFree.Tree.mul_assoc
import Submission.Work.ORHughesFree.Tree.one_mul
import Submission.Work.ORHughesFree.Tree.mul_one
import Submission.Work.ORHughesFree.Tree.left_distrib

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

noncomputable instance : AddCommMonoid Tree where
  add_assoc := Tree.add_assoc
  zero_add := Tree.zero_add
  add_zero := Tree.add_zero
  add_comm := Tree.add_comm
  nsmul := nsmulRec

noncomputable instance : CommMonoid Tree where
  mul_assoc := Tree.mul_assoc
  one_mul := Tree.one_mul
  mul_one := Tree.mul_one
  mul_comm := Tree.mul_comm

noncomputable instance : Distrib Tree where
  left_distrib := Tree.left_distrib
  right_distrib x y z := by
    rw [Tree.mul_comm (x + y) z, Tree.mul_comm x z, Tree.mul_comm y z, Tree.left_distrib]

end Work.ORHughesFree
