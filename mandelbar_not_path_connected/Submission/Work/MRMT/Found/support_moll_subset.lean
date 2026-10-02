import Mathlib
import Submission.Work.MRMT.Weyl.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Complex Function

/-- The support of the mollification `ρ ⋆ μ` (a convolution of a real-valued kernel `ρ` supported in
`closedBall 0 r` with a function `μ` supported in `closedBall 0 R`) is contained in
`closedBall 0 (r + R)`: the integrand `y ↦ (ρ y : ℂ) * μ (x - y)` vanishes pointwise whenever
`‖x‖ > r + R`, since `ρ y ≠ 0` forces `‖y‖ ≤ r` and `μ (x - y) ≠ 0` forces `‖x - y‖ ≤ R`. -/
theorem support_moll_subset {μ : ℂ → ℂ} {ρ : ℂ → ℝ} {r R : ℝ}
    (hρ : Function.support ρ ⊆ Metric.closedBall 0 r)
    (hμ : Function.support μ ⊆ Metric.closedBall 0 R) :
    Function.support (Work.MRMT.Weyl.moll ρ μ) ⊆ Metric.closedBall 0 (r + R) := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  push Not at hlt
  have hzero : ∀ y, (ρ y : ℂ) * μ (x - y) = 0 := by
    intro y
    by_cases hρy : ρ y = 0
    · simp [hρy]
    by_cases hμy : μ (x - y) = 0
    · simp [hμy]
    exfalso
    have hy : y ∈ Function.support ρ := hρy
    have hxy : x - y ∈ Function.support μ := hμy
    have hy_norm : ‖y‖ ≤ r := by
      have h1 := hρ hy
      rwa [Metric.mem_closedBall, dist_zero_right] at h1
    have hxy_norm : ‖x - y‖ ≤ R := by
      have h1 := hμ hxy
      rwa [Metric.mem_closedBall, dist_zero_right] at h1
    have hnorm : ‖x‖ ≤ r + R := by
      have h2 : ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      rw [h2]
      calc ‖(x - y) + y‖ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
        _ ≤ R + r := add_le_add hxy_norm hy_norm
        _ = r + R := by ring
    linarith
  have hmoll : Work.MRMT.Weyl.moll ρ μ x = 0 := by
    rw [Work.MRMT.Weyl.moll_apply]
    simp only [hzero, integral_zero]
  exact hx hmoll

end Work.MRMT.Found
