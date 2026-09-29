import Mathlib
import Submission.Work.TMComp.IDSDefs

namespace Work.TMComp.IDSPrufer

open Work.TMContract

/-- The Prüfer iterates form a cocycle: `F^{n+m}_x = F^m_{x+nα} ∘ F^n_x`. -/
theorem pruferIter_cocycle (α lam E x t : ℝ) (n m : ℕ) :
    Work.TMContract.pruferIter α lam E (n + m) x t
      = Work.TMContract.pruferIter α lam E m (x + (n : ℝ) * α)
          (Work.TMContract.pruferIter α lam E n x t) := by
  induction m with
  | zero => rw [Nat.add_zero, pruferIter]
  | succ m ih =>
    rw [Nat.add_succ, pruferIter, pruferIter, ih]
    have harg : x + ((n + m : ℕ) : ℝ) * α = (x + (n : ℝ) * α) + (m : ℝ) * α := by
      push_cast; ring
    rw [harg]

end Work.TMComp.IDSPrufer
