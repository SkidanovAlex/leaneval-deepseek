/-
# `|z^k · Gker k z| ≤ 10·k!/z` for `k ≤ 4` and `z ≥ 1`

`Gker k` is the closed form of the `k`-th derivative of the fundamental-model profile
`F_* (z) = 2z/(1+z)²` (`Submission.Work.FTS.LocData.FstarAux`):

  `Gker k z = 2·(-1)^k·k!·(z - k)/(1+z)^(k+2)`.

This module records the far-field decay of that family in the *weighted* form `z^k · Gker k z`,
which is exactly the quantity arising from the `k`-fold `D_z = z∂_z` iteration (each `D_z`
produces a factor `z`).  The bound is elementary: for `z ≥ 1` and `k ≤ 4` one has
`|z - k| ≤ z + k ≤ 5z` and `(1+z)^(k+2) ≥ z^(k+2)`, so

  `|z^k·Gker k z| = 2·k!·z^k·|z-k|/(1+z)^(k+2) ≤ 2·k!·5z^(k+1)/z^(k+2) = 10·k!/z`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.FTS.LocData.FstarAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real

namespace Work.FTS.LocData

set_option autoImplicit false

/-- **The far-field decay of `z^k·Gker k z`.**  For `k ≤ 4` and `z ≥ 1`,

  `|z^k · Gker k z| ≤ 10·k!/z`.

Since `Gker k z = 2(-1)^k k!(z-k)/(1+z)^(k+2)` and `(1+z)^(k+2) ≥ z^(k+2)`, while
`|z - k| ≤ z + k ≤ 5z` for `z ≥ 1`, `k ≤ 4`, this follows by immediate arithmetic. -/
theorem abs_zpow_mul_Gker_le (k : ℕ) (hk : k ≤ 4) {z : ℝ} (hz : 1 ≤ z) :
    |z ^ k * Work.FTS.LocData.Gker k z| ≤ 10 * (k.factorial : ℝ) / z := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hfac : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hzpow : (0 : ℝ) ≤ z ^ k := pow_nonneg hz0.le k
  have hden : (0 : ℝ) < (1 + z) ^ (k + 2) := pow_pos hz1 _
  -- `|z - k| ≤ 5z` because `z ≥ 1` and `k ≤ 4`
  have hkR : |z - (k : ℝ)| ≤ 5 * z := by
    have hk4 : (k : ℝ) ≤ 4 := by exact_mod_cast hk
    rw [abs_le]
    constructor <;> linarith
  -- pull out the sign `(-1)^k`
  have hsign : z ^ k * Gker k z =
      (-1 : ℝ) ^ k * (2 * (k.factorial : ℝ) * z ^ k * (z - (k : ℝ)) / (1 + z) ^ (k + 2)) := by
    rw [Gker_apply]
    ring
  rw [hsign, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_mul, abs_of_nonneg hfac,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hzpow]
  -- bound the numerator by `2·k!·z^k·5z`
  have step1 : 2 * (k.factorial : ℝ) * z ^ k * |z - (k : ℝ)| / (1 + z) ^ (k + 2)
      ≤ 2 * (k.factorial : ℝ) * z ^ k * (5 * z) / (1 + z) ^ (k + 2) := by
    gcongr
  -- and the denominator by `z^(k+2)`
  have step2 : 2 * (k.factorial : ℝ) * z ^ k * (5 * z) / (1 + z) ^ (k + 2)
      ≤ 10 * (k.factorial : ℝ) / z := by
    rw [div_le_div_iff₀ hden hz0]
    have h1 : 2 * (k.factorial : ℝ) * z ^ k * (5 * z) * z
        = 10 * (k.factorial : ℝ) * z ^ (k + 2) := by
      rw [pow_add]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0.le (by linarith) (k + 2))
      (by positivity)
  linarith

end Work.FTS.LocData
