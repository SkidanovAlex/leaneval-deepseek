import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.SmallBoxSliding.Sliding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.WB

/-- The FS `F`-remainder weight at `c = 1` is bounded by the affine function
`μ ^ 2 + μ * t` on the physical half-line `t ≥ 0`.  Writing
`psiWeight 1 μ t = (t - μ) ^ 2 / (1 + t / μ)` and using
`(μ ^ 2 + μ * t) * (1 + t / μ) = (t + μ) ^ 2`, this reduces to
`(t - μ) ^ 2 ≤ (t + μ) ^ 2`, i.e. `0 ≤ 4 t μ`. -/
theorem psiWeight_le_affine {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ ^ 2 + μ * t := by
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (by positivity)
    linarith
  rw [Work.SmallBoxSliding.psiWeight, one_mul, div_le_iff₀ hden]
  have key : (μ ^ 2 + μ * t) * (1 + t * μ⁻¹) = (t + μ) ^ 2 := by
    field_simp
    ring
  rw [key]
  nlinarith [mul_nonneg ht (le_of_lt hμ)]

end Work.BoseFixB1.WB
