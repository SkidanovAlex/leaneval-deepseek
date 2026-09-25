import Mathlib
import Submission.Work.Hormander.Weights.contDiff_dCoord
import Submission.Work.Hormander.Weights.contDiff_dPhi

namespace Work.Hormander.Weights

/-- For `u` of class `C²` and a real weight `φ` of class `C²`, the expression
`∂_j u - u·∂_j φ` (the `j`-component of `∂̄*_φ`-type brackets) is of class `C¹`:
`∂_j u` and `∂_j φ` are `C¹`, and the product of the `C¹` (indeed `C²`) function
`u` with `∂_j φ` is `C¹`. -/
theorem contDiff_delta {n : ℕ} (j : Fin n) {u : Cn n → ℂ} {φ : Cn n → ℝ}
    (hu : ContDiff ℝ 2 u) (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 1 (fun z => dCoord n j u z - u z * dPhi n j φ z) := by
  have h1 : ContDiff ℝ 1 (fun z => dCoord n j u z) := contDiff_dCoord j hu
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have h2 : ContDiff ℝ 1 (fun z => dPhi n j φ z) := contDiff_dPhi j hφ
  exact h1.sub (hu1.mul h2)

end Work.Hormander.Weights
