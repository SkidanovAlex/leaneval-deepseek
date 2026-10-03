import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.Tree.mul_comm
import Submission.Work.ORHughesFree.Tree.zero_mul

namespace Work.ORHughesFree.Tree

theorem mul_zero (x : Tree) : x * 0 = 0 := by
  rw [mul_comm x 0, zero_mul x]

end Work.ORHughesFree.Tree
