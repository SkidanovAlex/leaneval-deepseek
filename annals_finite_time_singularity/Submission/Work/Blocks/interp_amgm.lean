import Mathlib.Algebra.Order.Star.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Blocks

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The AM–GM and coefficient lemmas of the box assembly

The arithmetic core of the compact case of the two-dimensional mixed weighted interpolation
(`Work.Blocks.interp_mixed_compact_clean`).  After the per-slice estimate
(`Work.Blocks.interp_slice_DzG`) has been integrated against `w²` and the `z`-integral of
`J(z) = -∫_θ D_zG·∂_θ²(D_zG)σ` has been converted by the radial integration by parts
(`Work.Blocks.interp_z_ibp_clean`, side conditions `Work.Blocks.slice_Dz_support`,
`slice_pthIter2_support`, `slice_z_contDiffOn_one`) plus the Fubini swap
(`Work.Blocks.interp_swap_clean`) into the pairing `∫_θ(∫_z w² X Y)σ` with

  `X = D_z²G + b·D_zG`,   `b z = (z-3)/(1+z)`,   `Y = ∂_θ²G`,   `σ = sin(2θ)^{-η}`,

the estimate is closed by the two pointwise facts proved here:

* `abs_mul_le_alpha_sq`: `|X·Y| ≤ α²X² + Y²/(4α²)` (so `∫∫w²|X||Y|σ ≤ α²∫∫w²X²σ + (1/(4α²))∫∫w²Y²σ`);
* `sq_add_b_mul_sq_le`: `(X + b·Y)² ≤ 2X² + 18Y²` for `|b| ≤ 3` (so `∫∫w²X²σ ≤ 2 ddInt G + 18 dInt G`),

together with `abs_bcoef_le`: `|(z-3)/(1+z)| ≤ 3` for `z ≥ 0`.  Multiplying the resulting
inequality by `((1+η)/(1-η))` and using `α ≤ 1/4` (so that `α² ≤ α⁴/α²·const`, `1/(4α²) ≤ const/α⁴`
and `α² ≤ const`) produces the box statement `α² mixInt G ≤ C(α⁴ ddInt G + ttInt G + α² dInt G)`
of `Work.Blocks.interp_mixed_compact_clean`.
-/

/-- `|X·Y| ≤ α²X² + Y²/(4α²)` — the weighted AM–GM used for the mixed pairing. -/
theorem abs_mul_le_alpha_sq (α X Y : ℝ) (hα : 0 < α) :
    |X * Y| ≤ α ^ 2 * X ^ 2 + Y ^ 2 / (4 * α ^ 2) := by
  have hα2 : (0 : ℝ) < α ^ 2 := pow_pos hα 2
  have hYden : (0 : ℝ) < 4 * α ^ 2 := by positivity
  rw [abs_mul, ← sq_abs X, ← sq_abs Y]
  have hexp : (α * |X| - |Y| / (2 * α)) ^ 2
      = α ^ 2 * |X| ^ 2 - |X| * |Y| + |Y| ^ 2 / (4 * α ^ 2) := by
    have h2α : (2 : ℝ) * α ≠ 0 := by positivity
    have h4 : 4 * α ^ 2 ≠ 0 := ne_of_gt hYden
    field_simp
    ring
  have hsq : 0 ≤ α ^ 2 * |X| ^ 2 - |X| * |Y| + |Y| ^ 2 / (4 * α ^ 2) := by
    have := sq_nonneg (α * |X| - |Y| / (2 * α))
    rwa [hexp] at this
  linarith

/-- `(X + b·Y)² ≤ 2X² + 18Y²` for `|b| ≤ 3` — the coefficient estimate for `X = D_z²G + b·D_zG`. -/
theorem sq_add_b_mul_sq_le {X Y b : ℝ} (hb : |b| ≤ 3) :
    (X + b * Y) ^ 2 ≤ 2 * X ^ 2 + 18 * Y ^ 2 := by
  have h1 : (X + b * Y) ^ 2 ≤ 2 * X ^ 2 + 2 * (b * Y) ^ 2 := by
    nlinarith [sq_nonneg (X - b * Y)]
  have hb2 : b ^ 2 ≤ 9 := by
    have := abs_le.mp hb
    nlinarith [this.1, this.2]
  have h2 : (b * Y) ^ 2 ≤ 9 * Y ^ 2 := by
    rw [mul_pow]
    nlinarith [sq_nonneg Y]
  linarith

/-- The coefficient `b z = (z-3)/(1+z)` of the radial integration by parts is bounded by `3`
on the half-line `z ≥ 0`. -/
theorem abs_bcoef_le (z : ℝ) (hz : 0 ≤ z) : |(z - 3) / (1 + z)| ≤ 3 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos h1, div_le_iff₀ h1]
  have h2 : |z - 3| ≤ z + 3 := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith

end

end Work.Blocks
