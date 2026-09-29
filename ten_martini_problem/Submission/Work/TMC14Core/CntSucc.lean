import Mathlib
import Submission.Work.TMC14Core.Weyl

namespace Work.TMC14Core

/-- `cnt` as an explicit finite sum of indicator functions. -/
theorem cnt_eq_sum (b c : Bool) (n : ℕ) (f : Fin n → Bool × Bool) :
    cnt b c n f = ∑ i : Fin n, (if f i = (b, c) then 1 else 0) := by
  rw [cnt, Finset.card_filter]

theorem CntSucc (b c : Bool) (n : ℕ) (f : Fin (n + 1) → Bool × Bool) :
    cnt b c (n + 1) f = cnt b c n (fun i => f i.succ) + (if f 0 = (b, c) then 1 else 0) := by
  rw [cnt_eq_sum b c (n + 1) f, cnt_eq_sum b c n (fun i => f i.succ), Fin.sum_univ_succ]
  ring

end Work.TMC14Core
