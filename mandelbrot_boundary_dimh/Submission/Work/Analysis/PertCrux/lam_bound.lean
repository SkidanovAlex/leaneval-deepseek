import Mathlib

namespace Work.Analysis.PertCrux

/-- Numerical bound: with `Ξ' ≥ 10` and `MK, CW, RG ≤ Ξ'`, the crude upper bound
`10^6 * (Ξ' + MK + CW + RG + 1)^3 + 10^6` for `Λ` is dominated by `68922000 * Ξ'^3`.
The inequality is tight at the corner `Ξ' = MK = CW = RG = 10`, where
`(4*10+1)^3 + 1 = 41^3 + 1 = 68922 = 68922000/10^3`. -/
theorem lam_bound {Ξ' MK CW RG Λ : ℝ}
    (hΞ' : 10 ≤ Ξ') (hMKΞ : MK ≤ Ξ') (hCWΞ : CW ≤ Ξ') (hRGΞ : RG ≤ Ξ')
    (hΛUB : Λ ≤ 10 ^ 6 * (Ξ' + MK + CW + RG + 1) ^ 3 + 10 ^ 6) :
    Λ ≤ 68922000 * Ξ' ^ 3 := by
  -- the sum inside the cube is at most `4*Ξ' + 1`
  have hsum : Ξ' + MK + CW + RG + 1 ≤ 4 * Ξ' + 1 := by linarith
  -- `x ↦ x^3` is strictly increasing on `ℝ` (an odd power), no sign hypothesis needed
  have hcube : (Ξ' + MK + CW + RG + 1) ^ 3 ≤ (4 * Ξ' + 1) ^ 3 :=
    (Odd.pow_le_pow (by decide : Odd 3)).mpr hsum
  -- the numerical core, tight at `Ξ' = 10`
  have hkey : (10 : ℝ) ^ 6 * (4 * Ξ' + 1) ^ 3 + 10 ^ 6 ≤ 68922000 * Ξ' ^ 3 := by
    have hfac : 68922000 * Ξ' ^ 3 - (10 ^ 6 * (4 * Ξ' + 1) ^ 3 + 10 ^ 6)
        = 2000 * (Ξ' - 10) * (2461 * Ξ' ^ 2 + 610 * Ξ' + 100) := by ring
    have h1 : 0 ≤ Ξ' - 10 := by linarith
    have h2 : 0 ≤ 2461 * Ξ' ^ 2 + 610 * Ξ' + 100 := by nlinarith [sq_nonneg Ξ']
    nlinarith [hfac, mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2000) h1) h2]
  have hmul : (10 : ℝ) ^ 6 * (Ξ' + MK + CW + RG + 1) ^ 3 ≤ 10 ^ 6 * (4 * Ξ' + 1) ^ 3 :=
    mul_le_mul_of_nonneg_left hcube (by norm_num)
  linarith

end Work.Analysis.PertCrux
