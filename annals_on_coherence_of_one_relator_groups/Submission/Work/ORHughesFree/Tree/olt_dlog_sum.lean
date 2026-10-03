import Mathlib
import Submission.Work.ORHughesFree.Prop51.ConclB

namespace Work.ORHughesFree.Tree

/-- The `dlog`-bound is preserved by finite sums of trees: if every summand `t i` satisfies
`dlog (t i) < some A`, then the sum does too.  (The empty sum is `0`, whose `dlog` is `none`,
which is `< some A`.) -/
theorem olt_dlog_sum {ι : Type} (s : Finset ι) (t : ι → Work.ORHughesFree.Tree)
    (A : Work.ORHughesFree.Tree)
    (h : ∀ i ∈ s, Work.ORHughesFree.Tree.Olt (Work.ORHughesFree.Tree.dlog (t i)) (some A)) :
    Work.ORHughesFree.Tree.Olt (Work.ORHughesFree.Tree.dlog (∑ i ∈ s, t i)) (some A) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Work.ORHughesFree.Tree.dlog_zero]
    exact ⟨Work.ORHughesFree.Tree.ole_none_left _, Work.ORHughesFree.Tree.not_ole_some_none A⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine Work.ORHughesFree.Tree.ole_olt_trans
      (Work.ORHughesFree.Tree.ole_dlog_add (t a) (∑ i ∈ s, t i)) ?_
    exact Work.ORHughesFree.Tree.olt_omax_of (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Work.ORHughesFree.Tree
