import Mathlib
import Submission.Work.WilG4c.CellParamDefs

namespace Work.WilG4c

theorem append_eq_gluePt (p N : ℕ) (l : Fin p → ℝ) (y : Fin N → ℝ) :
    Fin.append l y = Work.WilG4c.gluePt p N 0 (Nat.zero_le N) l y := by
  funext i
  induction i using Fin.addCases with
  | left j =>
      rw [Fin.append_left]
      exact (Work.WilG4c.gluePt_idxL p N 0 (Nat.zero_le N) l y j).symm
  | right j =>
      rw [Fin.append_right]
      exact (Work.WilG4c.gluePt_idxR p N 0 (Nat.zero_le N) l y j).symm

end Work.WilG4c
