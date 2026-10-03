import Mathlib
import Submission.Work.ORHughesFree.Prop51.ConclB
import Submission.Work.ORHughesFree.Tree.exp_mono

namespace Work.ORHughesFree.Tree

/-- A tree strictly below `exp A` has `dlog` strictly below `some A`: if `x < exp A` then
`dlog x < some A` in the order on `Option Tree`.  Equivalently (by `dlog_exp` and
`lt_of_olt_dlog`), the double implication `x < exp A ↔ dlog x < some A` holds. -/
theorem olt_dlog_of_lt_exp {x A : Work.ORHughesFree.Tree}
    (h : Work.ORHughesFree.Tree.lt x (Work.ORHughesFree.Tree.exp A)) :
    Work.ORHughesFree.Tree.Olt (Work.ORHughesFree.Tree.dlog x) (some A) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [dlog_zero]
    exact ⟨ole_none_left _, not_ole_some_none A⟩
  · obtain ⟨a, ha⟩ := (Tree.log_spec x).2.2 hx0
    -- `log x = some a`, so `dlog x = some a`; it remains to show `a < A`.
    have hdlog : dlog x = some a := ha
    rw [hdlog]
    -- `exp a ≤ x < exp A`, so `exp a < exp A`, and `exp` reflects the strict order.
    exact ole_some_of_lt (Tree.lt_of_exp_lt_exp (lt_of_le_of_lt' (Tree.le_exp_log ha) h))

end Work.ORHughesFree.Tree
