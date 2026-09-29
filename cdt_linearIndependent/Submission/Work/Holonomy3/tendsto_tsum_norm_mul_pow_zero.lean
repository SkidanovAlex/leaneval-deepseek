import Mathlib
import Submission.Work.Holonomy3.cleared_defs

namespace Work.Holonomy3

open Filter Topology
open scoped BigOperators

/-- For a power series `Φ` over `ℂ` with vanishing constant term whose coefficient norms satisfy
`∑ ‖coeff j Φ‖ * r ^ j < ∞` for some `r > 0`, the real function
`t ↦ ∑' j, ‖coeff j Φ‖ * t ^ j` tends to `0` as `t → 0` through positive reals.

This is the (absolute) holomorphic-continuation fact that the norm series converges to `0` at the
origin; the hypothesis `h0` is essential since otherwise the limit is `‖coeff 0 Φ‖`. -/
theorem tendsto_tsum_norm_mul_pow_zero {Φ : PowerSeries ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : PowerSeries.coeff 0 Φ = 0)
    (h : Summable (fun j : ℕ => ‖PowerSeries.coeff j Φ‖ * r ^ j)) :
    Filter.Tendsto (fun t : ℝ => ∑' j : ℕ, ‖PowerSeries.coeff j Φ‖ * t ^ j)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  let F : ℝ → ℝ := fun t => ∑' j : ℕ, ‖PowerSeries.coeff j Φ‖ * t ^ j
  change Filter.Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
  -- The norm series is continuous on `[0, r]` by the Weierstrass M-test, with majorant
  -- `u j = ‖coeff j Φ‖ * r ^ j`.
  have hcont : ContinuousOn F (Set.Icc 0 r) := by
    change ContinuousOn (fun t : ℝ => ∑' j : ℕ, ‖PowerSeries.coeff j Φ‖ * t ^ j) _
    apply continuousOn_tsum (u := fun j : ℕ => ‖PowerSeries.coeff j Φ‖ * r ^ j)
    · intro i
      exact (continuous_const.mul (continuous_pow i)).continuousOn
    · exact h
    · intro n x hx
      have hx0 : 0 ≤ x := hx.1
      have hxr : x ≤ r := hx.2
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hx0 n))]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hxr n) (norm_nonneg _)
  -- Value at the origin: only the `j = 0` term survives, and `coeff 0 Φ = 0`.
  have hF0 : F 0 = 0 := by
    change (∑' j : ℕ, ‖PowerSeries.coeff j Φ‖ * (0 : ℝ) ^ j) = 0
    rw [tsum_eq_single 0]
    · simp [h0]
    · intro j hj
      rw [zero_pow hj, mul_zero]
  -- `nhdsWithin 0 (Ioi 0)` is coarser than `nhdsWithin 0 (Icc 0 r)`.
  have hle : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin (0 : ℝ) (Set.Icc 0 r) := by
    rw [nhdsWithin_le_iff, mem_nhdsWithin]
    exact ⟨Set.Iio r, isOpen_Iio, hr, fun x hx => ⟨le_of_lt hx.2, le_of_lt hx.1⟩⟩
  have hcw : Filter.Tendsto F (nhdsWithin (0 : ℝ) (Set.Icc 0 r)) (nhds (F 0)) :=
    hcont.continuousWithinAt ⟨le_refl 0, hr.le⟩
  rw [hF0] at hcw
  exact hcw.mono_left hle

end Work.Holonomy3
