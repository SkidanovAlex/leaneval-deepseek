import Mathlib

namespace Work.RPB1a

/-- If the derivative of `u : ℝ → ℂ` is continuous and nowhere zero, then on the
compact interval `[0, 2π]` the norm of the derivative is bounded below by a
positive constant: a continuous nonvanishing function on a compact set attains
its minimum value there, and that minimum is positive. -/
theorem deriv_min_pos (u : ℝ → ℂ) (hu : Continuous (deriv u)) (hreg : ∀ t : ℝ, deriv u t ≠ 0) :
    ∃ m > 0, ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), m ≤ ‖deriv u t‖ := by
  obtain ⟨x₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by positivity : (0 : ℝ) ≤ 2 * Real.pi))
    (continuous_norm.comp hu).continuousOn
  exact ⟨‖deriv u x₀‖, norm_pos_iff.mpr (hreg x₀), fun t ht => hmin ht⟩

end Work.RPB1a
