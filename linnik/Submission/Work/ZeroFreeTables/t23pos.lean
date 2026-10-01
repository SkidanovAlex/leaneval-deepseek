import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs

namespace Work.ZeroFreeTables

/-- Every scale occurring in the rows of Tables 2 and 3 (and the supplementary rows `rowG`) is
positive.  This is a finite check over the explicitly listed row data: the first coordinate of
each row is a positive rational. -/
theorem t23pos : Work.ZeroFreeTables.T23Pos := by
  intro p hp
  have h : (t23rows ++ rowG).Forall (fun q => 0 < q.1) := by
    simp only [t23rows, rowA, rowB, rowC, rowD, rowE, rowF, rowG, List.forall_append,
      List.forall_cons]
    norm_num
  exact (List.forall_iff_forall_mem.mp h) p hp

end Work.ZeroFreeTables
