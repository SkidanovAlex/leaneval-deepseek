import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

/-- Weighted AM–GM with real exponents: since `(l/2 · s^{-η}) · ((2l)^{-1} · s^{η}) = 1/4`,
the quadratic `l/2 · s^{-η} · y² + (2l)^{-1} · s^{η}` dominates `2·(1/2)·|y| = |y|`.
This is the "absorb `|y|` into `ε y² + C(ε)`" inequality with `ε = l/2 · s^{-η}`. -/
theorem amgmRpow {η l s y : ℝ} (hη : 0 ≤ η) (hl : 0 < l) (hs : 0 < s) :
    |y| ≤ l / 2 * (s ^ (-η) * y ^ 2) + (2 * l)⁻¹ * s ^ η := by
  have _hη := hη
  -- `s^{-η} · s^{η} = 1`.
  have hmul : s ^ (-η) * s ^ η = 1 := by
    rw [← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero]
  -- the key product identity `(l/2 · s^{-η}) · ((2l)^{-1} · s^{η}) = 1/4`.
  have hab : (l / 2 * s ^ (-η)) * ((2 * l)⁻¹ * s ^ η) = 1 / 4 := by
    rw [show l / 2 * s ^ (-η) * ((2 * l)⁻¹ * s ^ η)
        = (l / 2 * (2 * l)⁻¹) * (s ^ (-η) * s ^ η) by ring]
    rw [hmul, mul_one]
    field_simp
    ring
  have ha : 0 < l / 2 * s ^ (-η) := by positivity
  -- AM–GM without division: `4a·(a·|y|² + b - |y|) = (2a·|y| - 1)² ≥ 0` because `4ab = 1`.
  have hid : 4 * (l / 2 * s ^ (-η)) * ((l / 2 * s ^ (-η)) * |y|^2 - |y| + (2 * l)⁻¹ * s ^ η)
      = (2 * (l / 2 * s ^ (-η)) * |y| - 1)^2 := by
    have h4 : 4 * (l / 2 * s ^ (-η)) * ((2 * l)⁻¹ * s ^ η) = 1 := by linarith [hab]
    nlinarith [h4]
  have hnn : 0 ≤ (l / 2 * s ^ (-η)) * |y|^2 - |y| + (2 * l)⁻¹ * s ^ η := by
    have h1 : 0 ≤ 4 * (l / 2 * s ^ (-η))
        * ((l / 2 * s ^ (-η)) * |y|^2 - |y| + (2 * l)⁻¹ * s ^ η) := by
      rw [hid]; exact sq_nonneg _
    exact nonneg_of_mul_nonneg_right h1 (by linarith [ha])
  nlinarith [hnn, sq_abs y]

end Work.FTS.EllSol
