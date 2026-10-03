import Mathlib


set_option linter.unusedVariables false
namespace Work.Pert

/-- Differentiability of the shifted composition `u ↦ Φ (z₀ + u)` on a closed ball around `0`,
from differentiability of `Φ` on an open `Q ⊇ closedBall z₀ r`. -/
theorem differentiableOn_comp_shift {Φ : ℂ → ℂ} {Q : Set ℂ} {z₀ : ℂ} {r : ℝ}
    (hQ : IsOpen Q) (hsub : Metric.closedBall z₀ r ⊆ Q) (hΦ : DifferentiableOn ℂ Φ Q) :
    DifferentiableOn ℂ (fun u : ℂ => Φ (z₀ + u)) (Metric.closedBall (0 : ℂ) r) := by
  have hshift : DifferentiableOn ℂ (fun u : ℂ => z₀ + u) (Metric.closedBall (0 : ℂ) r) :=
    differentiableOn_id.const_add z₀
  have hmaps : Set.MapsTo (fun u : ℂ => z₀ + u) (Metric.closedBall (0 : ℂ) r) Q := by
    intro u hu
    apply hsub
    rw [Metric.mem_closedBall] at hu ⊢
    simpa using hu
  exact hΦ.comp hshift hmaps

end Work.Pert
