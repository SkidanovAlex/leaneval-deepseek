import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

theorem isOpen_annulus (ρ : ℝ) : IsOpen (annulus ρ) := by
  have h1 : IsOpen {w : ℂ | ρ < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have h2 : IsOpen {w : ℂ | ‖w‖ < ρ⁻¹} := isOpen_lt continuous_norm continuous_const
  have h : annulus ρ = {w : ℂ | ρ < ‖w‖} ∩ {w : ℂ | ‖w‖ < ρ⁻¹} := rfl
  rw [h]
  exact h1.inter h2

end Work.RPB1a
