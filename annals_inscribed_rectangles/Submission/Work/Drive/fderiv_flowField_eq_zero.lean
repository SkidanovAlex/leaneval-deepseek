import Mathlib
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.cofactorVec_mem_ker

namespace Work.Drive

/-- The flow field of `F` is tangential: the derivative of `F` kills it. -/
theorem fderiv_flowField_eq_zero {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m}
    (x : Work.Drive.Amb m) : fderiv ℝ F x (Work.Drive.flowField F x) = 0 := by
  have hker : fderiv ℝ F x (cofactorVectorF F x) = 0 := cofactorVec_mem_ker (fderiv ℝ F x)
  rw [flowField, map_smul, map_smul, hker, smul_zero, smul_zero]

end Work.Drive
