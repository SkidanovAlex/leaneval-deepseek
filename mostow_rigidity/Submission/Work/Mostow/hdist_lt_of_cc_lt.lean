import Mathlib
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.Hyper

namespace Work.Mostow

/-- If the cosh-kernel `cc u v = cosh (hdist u v)` is below `cosh η` with `η > 0`, then the
hyperbolic distance is below `η`. -/
theorem hdist_lt_of_cc_lt {n : ℕ} {u v : Submission.Mostow.E n} {η : ℝ} (hη : 0 < η)
    (h : Submission.Mostow.Hyper.cc u v < Real.cosh η) :
    Submission.Mostow.hdist u v < η := by
  have h1 : Real.cosh (Submission.Mostow.hdist u v) < Real.cosh η := by
    rw [cosh_hdist]
    exact h
  have h2 : |Submission.Mostow.hdist u v| < |η| := Real.cosh_lt_cosh.mp h1
  rwa [abs_of_nonneg (hdist_nonneg u v), abs_of_pos hη] at h2

end Work.Mostow
