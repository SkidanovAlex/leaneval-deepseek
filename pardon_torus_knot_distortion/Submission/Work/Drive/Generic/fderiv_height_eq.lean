import Mathlib
import Submission.Work.Drive.Generic.HeightDefs

namespace Work.Drive.Generic

theorem fderiv_height_eq {Φ : ℝ × ℝ → Work.Drive.Generic.E3} (hΦ : ContDiff ℝ 3 Φ)
    (v : Work.Drive.Generic.E3) (p w : ℝ × ℝ) :
    fderiv ℝ (fun q => inner ℝ v (Φ q)) p w = inner ℝ v (fderiv ℝ Φ p w) := by
  rw [fderiv_inner_apply (𝕜 := ℝ) (f := fun _ : ℝ × ℝ => v)]
  · simp
  · exact differentiableAt_const v
  · exact (hΦ.differentiable (by norm_num)).differentiableAt

end Work.Drive.Generic
