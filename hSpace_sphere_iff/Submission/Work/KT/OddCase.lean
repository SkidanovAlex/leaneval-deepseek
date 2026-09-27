import Mathlib
import Submission.Work.KT.hopf_K
import Submission.Work.KT.odd_of_hopfOddK

namespace Work.KT

/-- The odd case of `hSpace_sphere_iff`: an H-space structure on `S^(2k+1)` forces
`k + 1 ∈ {1, 2, 4}` (Hopf construction + Adams operations). -/
theorem hSpace_odd_case (n : ℕ) (ho : Odd n)
    (h : Nonempty (HSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) :
    n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7 := by
  obtain ⟨k, rfl⟩ := ho
  obtain ⟨hS⟩ := h
  have hS' : HSpace (Sph (Eu (k + 1))) := hS
  obtain ⟨f, hf⟩ := hopf_K (k + 1) (by omega) hS'
  rcases odd_of_hopfOddK (k + 1) (by omega) f hf with h1 | h1 | h1 <;> omega

end Work.KT
