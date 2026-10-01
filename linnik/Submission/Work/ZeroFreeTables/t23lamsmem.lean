import Mathlib
import Submission.Work.ZeroFreeTables.t23Defs

namespace Work.ZeroFreeTables

/-- Every row scale occurring in `t23rows ++ rowG` is a member of the scale list `t23lams`:
a finite check on the literal row data. -/
theorem t23lamsmem : Work.ZeroFreeTables.T23LamsMem := by
  intro p hp
  simp only [t23rows, List.mem_append, or_assoc] at hp
  rcases hp with h | h | h | h | h | h | h
  all_goals (fin_cases h <;> norm_num [t23lams])

end Work.ZeroFreeTables
