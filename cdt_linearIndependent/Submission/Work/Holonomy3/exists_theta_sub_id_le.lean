import Mathlib
import Submission.Work.Holonomy3.model_deps

namespace Work.Holonomy3

/-- Global form of the prime number estimate for `θ`: for every `ε > 0` there is a nonnegative
constant `C` with `|θ y - y| ≤ ε * y + C` for all `y ≥ 0`.  (For `y ≥ Y` this is the relative form
`Commons.NumberTheory.Chebyshev.theta_rel_error`; for `0 ≤ y ≤ Y` the absolute constant
`C = θ Y + Y` suffices, using `Chebyshev.theta_mono` and `θ ≥ 0`.) -/
theorem exists_theta_sub_id_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 ≤ y →
      |Chebyshev.theta y - y| ≤ ε * y + C := by
  obtain ⟨Y₀, hY₀⟩ := Commons.NumberTheory.Chebyshev.theta_rel_error ε hε
  have hC : 0 ≤ Chebyshev.theta (max Y₀ 0) + max Y₀ 0 :=
    add_nonneg (Chebyshev.theta_nonneg _) (le_max_right _ _)
  refine ⟨Chebyshev.theta (max Y₀ 0) + max Y₀ 0, hC, ?_⟩
  intro y hy
  by_cases h : max Y₀ 0 ≤ y
  · -- large `y`: the relative form is available
    have hrel := hY₀ y (le_trans (le_max_left _ _) h)
    have h0 : 0 ≤ ε * y := mul_nonneg hε.le hy
    linarith
  · -- small `y`: use monotonicity of `θ` and `θ ≥ 0` to bound by the constant
    have hyY : y ≤ max Y₀ 0 := le_of_lt (not_le.mp h)
    have hmono : Chebyshev.theta y ≤ Chebyshev.theta (max Y₀ 0) :=
      Chebyshev.theta_mono hyY
    have hle : |Chebyshev.theta y - y| ≤ Chebyshev.theta (max Y₀ 0) + max Y₀ 0 := by
      rw [abs_le]
      constructor <;> linarith [Chebyshev.theta_nonneg y, hy, hmono]
    have h0 : 0 ≤ ε * y := mul_nonneg hε.le hy
    linarith

end Work.Holonomy3
