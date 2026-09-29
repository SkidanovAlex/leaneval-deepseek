import Mathlib
import Submission.Work.TMC16Core.Basic.pd_cheb_cont

namespace Work.TMC16Core.Basic

theorem pd_eq_contSeq (α lam θ : ℝ) (E : ℂ) (k : ℕ) :
    Work.TMC16Core.pd α lam θ E k = Work.TMC16Core.Cheb.contSeq (fun n => E - ((Work.TMC16Core.amoPot α lam θ ((n : ℕ) : ℤ) : ℝ) : ℂ)) k := by
  induction k using Nat.twoStepInduction with
  | zero => rw [Work.TMC16Core.pd.eq_1, Work.TMC16Core.Cheb.contSeq.eq_1]
  | one => rw [Work.TMC16Core.pd.eq_2, Work.TMC16Core.Cheb.contSeq.eq_2]
  | more n ih1 ih2 =>
    rw [Work.TMC16Core.pd.eq_3, Work.TMC16Core.Cheb.contSeq.eq_3, ih1, ih2]

end Work.TMC16Core.Basic
