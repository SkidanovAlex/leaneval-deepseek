import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB6Est.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The FS-regime value of `lhyEps`

Instance of `Work.BoseB6.lhyEps` (`eq:LebesgueError-Total`) at the parameters of
`fsRegime_fs`:

`a = X^{323/3}`, `R = 0`, `εT = X^{23/4}`, `K_ℓ = X^{-3/2}`, `s = X`, `d = X^6`, `μ = 1`.

Since `√R = 0` kills the first term and the remaining powers combine as

* `(K_ℓ s)⁻¹ = X^{1/2}`,
* `K_ℓ d s / (μ a³)^{1/2} = X^{-156}`,
* `X^{23/4} (K_ℓ d s)⁻¹ = X^{1/4}`,

the definition collapses to `X^{23/4} + X^{1/2}(1 + 162 log X⁻¹) + X^{1/4}(1 + 156 log X⁻¹)`.
-/

namespace Work.BoseB6Est.fsRegimeArith

theorem lhyEps_fs (X : ℝ) (hX : 0 < X) :
    Work.BoseB6.lhyEps (X ^ (323 / 3 : ℝ)) 0 (X ^ (23 / 4 : ℝ)) (X ^ (-(3 / 2) : ℝ)) X (X ^ 6) 1
      = X ^ (23 / 4 : ℝ) + X ^ (1 / 2 : ℝ) * (1 + 162 * Real.log X⁻¹)
        + X ^ (1 / 4 : ℝ) * (1 + 156 * Real.log X⁻¹) := by
  have hX0 : X ≠ 0 := ne_of_gt hX
  have hXnn : (0 : ℝ) ≤ X := hX.le
  -- `K_ℓ s = X^{-1/2}`, so `(K_ℓ s)⁻¹ = X^{1/2}`
  have hKl : (X ^ (-(3 / 2) : ℝ) * X)⁻¹ = X ^ (1 / 2 : ℝ) := by
    have h1 : X ^ (-(3 / 2) : ℝ) * X = X ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_add_one hX0 (-(3 / 2))]
      norm_num
    rw [h1, ← Real.rpow_neg hXnn (-(1 / 2) : ℝ), neg_neg]
  -- `K_ℓ d s = X^{11/2}`, so `(K_ℓ d s)⁻¹ = X^{-11/2}`
  have hKd : (X ^ (-(3 / 2) : ℝ) * X ^ 6 * X)⁻¹ = X ^ (-(11 / 2) : ℝ) := by
    have h2 : X ^ (-(3 / 2) : ℝ) * X ^ 6 * X = X ^ (11 / 2 : ℝ) := by
      rw [← Real.rpow_natCast X 6]
      rw [← Real.rpow_add hX]
      rw [← Real.rpow_add_one hX0]
      norm_num
    rw [h2, ← Real.rpow_neg hXnn (11 / 2 : ℝ)]
  -- the logarithmic argument `K_ℓ d s / (μ a³)^{1/2} = X^{-156}`
  have harg : X ^ (-(3 / 2) : ℝ) * X ^ 6 * X / (1 * (X ^ (323 / 3 : ℝ)) ^ 3) ^ (1 / 2 : ℝ)
      = X ^ (-156 : ℝ) := by
    have h2 : X ^ (-(3 / 2) : ℝ) * X ^ 6 * X = X ^ (11 / 2 : ℝ) := by
      rw [← Real.rpow_natCast X 6]
      rw [← Real.rpow_add hX]
      rw [← Real.rpow_add_one hX0]
      norm_num
    have hden : (1 * (X ^ (323 / 3 : ℝ)) ^ 3) ^ (1 / 2 : ℝ) = X ^ (323 / 2 : ℝ) := by
      rw [one_mul]
      have h1 : (X ^ (323 / 3 : ℝ)) ^ 3 = X ^ (323 : ℝ) := by
        rw [← Real.rpow_mul_natCast hXnn (323 / 3 : ℝ) 3]
        norm_num
      rw [h1, ← Real.rpow_mul hXnn 323 (1 / 2 : ℝ)]
      norm_num
    rw [h2, hden, ← Real.rpow_sub hX]
    norm_num
  -- `log d⁻¹ = -6 log X`
  have hlog6 : Real.log (X ^ 6)⁻¹ = -(6 * Real.log X) := by
    rw [Real.log_inv, Real.log_pow]
    ring
  -- `X^{23/4} (K_ℓ d s)⁻¹ = X^{1/4}`
  have hprod : X ^ (23 / 4 : ℝ) * X ^ (-(11 / 2) : ℝ) = X ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hX]
    norm_num
  unfold Work.BoseB6.lhyEps
  rw [Real.sqrt_zero, mul_zero, zero_add]
  rw [hKl, hKd, harg, hlog6, Real.log_rpow hX (-156), Real.log_inv X, hprod]
  ring

end Work.BoseB6Est.fsRegimeArith
