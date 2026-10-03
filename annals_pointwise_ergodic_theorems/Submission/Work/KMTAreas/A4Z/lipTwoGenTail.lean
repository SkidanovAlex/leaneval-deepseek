import Mathlib
import Submission.Work.KMTAreas.A4Z.smallTailBranch
import Submission.Work.KMTAreas.A4Z.largeTail

namespace Work.KMTAreas.A4Z

theorem lipTwoGenTail (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (hPel : Work.KMTContract.PeluseInverseKMT P) : ∀ (A : ℝ), 1 ≤ A → ∃ C K C0 K2 : ℝ, 0 < C ∧ 0 < K ∧ 0 < C0 ∧ 0 < K2 ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → Work.KMTAreas.A4Z.LipOutputGenTwoTail P ρ A C K C0 K2 := by
  exact glue P hP (smallTailBranch P) (largeTail P hP hPel)

end Work.KMTAreas.A4Z
