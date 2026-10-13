import Mathlib
import Submission.Work.WilE9G.Amb

namespace Work.WilE9G.Assembly

/-- At any point of a `Good` ambient stratum the `j × N` Jacobian matrix of the defining
equations has rank `j`; since a matrix with `N` columns has rank at most `N`, a nonempty
`Good` stratum has `j ≤ N`. -/
theorem ambStratum_j_le_ambient {N : ℕ} (S : Work.WilE9G.AmbStratum N) (hS : S.Good)
    (hne : S.X.set.Nonempty) : S.j ≤ N := by
  obtain ⟨z, hz⟩ := hne
  rw [← Work.WilE9G.AmbStratum_rank S hS hz]
  exact Matrix.rank_le_width _

end Work.WilE9G.Assembly
