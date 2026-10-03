import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.Tree.mul_comm
import Submission.Work.ORHughesFree.Tree.one_mul

set_option autoImplicit false

namespace Work.ORHughesFree.Tree

/-- `x * 1 = x`: the one-edge tree `1 = exp 0` is a right identity for the multiplication on
finite rooted trees.  This is immediate from the commutativity of `*` (`Tree.mul_comm`) and
`Tree.one_mul`. -/
theorem mul_one (x : Tree) : x * 1 = x := by
  rw [mul_comm x 1, one_mul x]

end Work.ORHughesFree.Tree
