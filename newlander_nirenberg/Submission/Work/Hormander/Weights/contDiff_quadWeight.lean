import Mathlib
import Submission.Work.Hormander.Weights.Defs

namespace Work.Hormander.Weights

theorem contDiff_quadWeight {n : ℕ} (K : ℝ) : ContDiff ℝ ⊤ (quadWeight n K) := by
  have h1 : ContDiff ℝ ⊤ (fun z : Cn n => ‖z‖ ^ 2) :=
    (contDiff_id : ContDiff ℝ ⊤ (id : Cn n → Cn n)).norm_sq (𝕜 := ℂ)
  have h : ContDiff ℝ ⊤ (fun z : Cn n => K * ‖z‖ ^ 2) := contDiff_const.mul h1
  change ContDiff ℝ ⊤ (fun z : Cn n => K * ‖z‖ ^ 2)
  exact h

end Work.Hormander.Weights
