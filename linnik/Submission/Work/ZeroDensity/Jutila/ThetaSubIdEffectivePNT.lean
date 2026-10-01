import Mathlib
import Submission.Work.LinnikAreas.Density4.ThetaPNTImports
import Submission.Commons.NumberTheory.Chebyshev.theta_abs_sub_id_le

namespace Work.ZeroDensity.Jutila

/-- **Effective PNT for `θ` (Chebyshev's theta)**: there are constants `C > 0` and
`x₀ ≥ 2` with `|θ t − t| ≤ C · t / log t` for all `t ≥ x₀`.

This is a direct corollary of the shared estimate
`Commons.NumberTheory.Chebyshev.theta_sub_id_le_log`, which supplies the sharp
constant `C = 1`. -/
theorem ThetaSubIdEffectivePNT :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧ ∀ t : ℝ, x₀ ≤ t →
      |Chebyshev.theta t - t| ≤ C * t / Real.log t := by
  obtain ⟨x₀, hx₀2, hθ⟩ := Commons.NumberTheory.Chebyshev.theta_sub_id_le_log
  exact ⟨1, x₀, one_pos, hx₀2, fun t ht => by simpa using hθ t ht⟩

end Work.ZeroDensity.Jutila
