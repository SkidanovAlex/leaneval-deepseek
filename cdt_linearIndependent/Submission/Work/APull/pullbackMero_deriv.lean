import Mathlib
import Submission.Work.CPull.exists_poly_mul_holo_div
import Submission.Work.CPull.defs
import Submission.Work.CPull.pullbackMero_deriv_iter

namespace Work.APull

/-- `dY f` is the formal derivative `(PowerSeries.derivative (R := ℚ)) f`. -/
lemma dY_eq_derivative (f : PowerSeries ℚ) :
    Submission.CDTPlan.dY f = (PowerSeries.derivative (R := ℚ)) f := rfl

theorem pullbackMero_deriv {f : PowerSeries ℚ} {φ : ℂ → ℂ} (S : Finset ℂ)
    (hφ : DifferentiableOn ℂ φ (Metric.ball 0 1)) (hφ0 : φ 0 = 0) (hφ'0 : deriv φ 0 ≠ 0)
    (hS : ∀ z ∈ Metric.ball (0 : ℂ) 1, deriv φ z = 0 → z ∈ S)
    (h : Submission.CDTPlan.PullbackMero f φ) :
    Submission.CDTPlan.PullbackMero (Submission.CDTPlan.dY f) φ := by
  rw [dY_eq_derivative]
  exact Work.CPull.pullbackMero_deriv_step S hφ hφ'0 hS h

end Work.APull
