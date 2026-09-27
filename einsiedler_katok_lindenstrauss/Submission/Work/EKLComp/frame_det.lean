import Mathlib
import Submission.Work.EKLComp.FrameDefs

namespace Work.EKLComp

/-- The determinant of the first Givens rotation `MA v` is `ca v ^ 2 + cb v ^ 2 = 1`. -/
lemma MA_det (v : Fin 3 → ℝ) : (MA v).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [MA]
  nlinarith [ca_sq_add_cb_sq v]

/-- The determinant of the second Givens rotation `MB v` is `cc v ^ 2 + cd v ^ 2 = 1`. -/
lemma MB_det (v : Fin 3 → ℝ) (hv : v ≠ 0) : (MB v).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [MB]
  nlinarith [cc_sq_add_cd_sq v hv]

theorem frame_det (v : Fin 3 → ℝ) (hv : v ≠ 0) : (Work.EKLComp.Mmat v).det = 1 := by
  rw [Mmat, Matrix.det_mul, MA_det v, MB_det v hv, mul_one]

end Work.EKLComp
