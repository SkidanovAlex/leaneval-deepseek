import Mathlib
import Submission.Work.Resample.defs
import Submission.Work.Resample.tensorComp

namespace Work.Resample

theorem tensorChain (ss ts : List ℕ) (α : ℕ) (h : ss.length = ts.length) (u : Fin ss.prod → ℂ) :
    Work.Resample.tensorLin ss ss (fun i j k => ∑ l : Fin (ts.getD i 0),
        Work.Resample.rB (ss.getD i 0) (ts.getD i 0) α j l *
          (∑ l2 : Fin (ts.getD i 0), Work.Resample.dE (ts.getD i 0) l l2 *
            Work.Resample.rA (ss.getD i 0) (ts.getD i 0) α l2 k)) u
      = Work.Resample.resBop ss ts α (Work.Resample.dftOp ts (Work.Resample.resAop ss ts α u)) := by
  rw [tensorComp ss ts ss h h.symm
      (fun i j l => rB (ss.getD i 0) (ts.getD i 0) α j l)
      (fun i l k => ∑ l2 : Fin (ts.getD i 0), dE (ts.getD i 0) l l2 * rA (ss.getD i 0) (ts.getD i 0) α l2 k) u]
  rw [tensorComp ss ts ts h rfl
      (fun i l k => dE (ts.getD i 0) l k)
      (fun i l k => rA (ss.getD i 0) (ts.getD i 0) α l k) u]
  rfl

end Work.Resample
