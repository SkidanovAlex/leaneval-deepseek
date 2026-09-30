import Mathlib
import Submission.Work.BMF.liouville.vk_large_defs
import Submission.Work.BMF.liouville.one_sub_inv_pow_le_exp_neg
import Submission.Work.BMF.liouville.exp_neg_nine_le
import Submission.Work.BMF.liouville.exp_neg_34_5_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Stechkin excess of the large-`λ` Vinogradov extraction is at most `λ²/40`

`dDelta lam = k²/2·(1−1/k)^{r'} + g²/2·(1−1/g)^{s'}` is the total excess of the two Stechkin
inputs of `vk_large_defs`, where (with `λ = log t / log N` and `λ ≥ 13/5`)

`g = ⌈5λ⌉`, `k = g+1`, `r' = ⌈300λ²/k⌉`, `s' = ⌈200λ²/g⌉`.

Writing `w₁ = λ/k` and `w₂ = λ/g`, the elementary bound `(1 − 1/n)^m ≤ exp(−m/n)`
(`one_sub_inv_pow_le_exp_neg`) together with `r' ≥ 300λ²/k` and `s' ≥ 200λ²/g` gives

`k²/2·(1−1/k)^{r'} ≤ λ² · exp(−300w₁²)/(2w₁²)`,  `g²/2·(1−1/g)^{s'} ≤ λ² · exp(−200w₂²)/(2w₂²)`.

The ceilings give `5λ ≤ g < 5λ+1`, `5λ+1 ≤ k < 5λ+2`, hence `w₁ ≥ 13/75` and `w₂ ≥ 13/70`; so
`300w₁² ≥ 9` and `200w₂² ≥ 34/5`, while `k ≤ (75/13)λ` and `g ≤ (70/13)λ`. Therefore

`dDelta lam ≤ λ²·((75/13)²/2·e^{−9} + (70/13)²/2·e^{−34/5}) ≤ λ²/40`,

the last step using `e^{−9} ≤ 1/7000` (`exp_neg_nine_le`) and `e^{−34/5} ≤ 1/800`
(`exp_neg_34_5_le`), together with `(5625/338)/7000 + (4900/338)/800 < 1/40`.
-/

namespace Work.BMF.liouville

open scoped BigOperators

/-- The total Stechkin excess `Δ₁ + Δ₂` is at most `λ²/40`. -/
theorem vk_large_delta_bound (lam : ℝ) (hlam : 13/5 ≤ lam) : dDelta lam ≤ lam ^ 2 / 40 := by
  have h5lam0 : (0 : ℝ) ≤ 5 * lam := by linarith
  have hGle : 5 * lam ≤ (dG lam : ℝ) := by simpa [dG] using Nat.le_ceil (5 * lam)
  have hGlt : (dG lam : ℝ) < 5 * lam + 1 := by
    simpa [dG] using Nat.ceil_lt_add_one h5lam0
  have hKcast : (dK lam : ℝ) = (dG lam : ℝ) + 1 := by simp [dK]
  have hGpos : (0 : ℝ) < (dG lam : ℝ) := by linarith
  have hKpos : (0 : ℝ) < (dK lam : ℝ) := by linarith
  have hG2 : 2 ≤ dG lam := by
    have : (2 : ℝ) ≤ (dG lam : ℝ) := by linarith
    exact_mod_cast this
  have hK2 : 2 ≤ dK lam := by
    have : (2 : ℝ) ≤ (dK lam : ℝ) := by linarith
    exact_mod_cast this
  have hrp : 300 * lam ^ 2 / (dK lam : ℝ) ≤ (dRp lam : ℝ) := by
    simpa [dRp] using Nat.le_ceil (300 * lam ^ 2 / (dK lam : ℝ))
  have hsp : 200 * lam ^ 2 / (dG lam : ℝ) ≤ (dSp lam : ℝ) := by
    simpa [dSp] using Nat.le_ceil (200 * lam ^ 2 / (dG lam : ℝ))
  -- The ceilings dominate the quantities appearing in the exponents.
  have hnum1 : 9 * (dK lam : ℝ) ^ 2 ≤ 300 * lam ^ 2 := by
    have hKle : (dK lam : ℝ) ≤ 5 * lam + 2 := by linarith
    have hKnn : (0 : ℝ) ≤ (dK lam : ℝ) := le_of_lt hKpos
    have h5l2 : (0 : ℝ) ≤ 5 * lam + 2 := by linarith
    nlinarith [hKle, hKnn, h5l2, hlam, sq_nonneg (lam - 13 / 5)]
  have hnum2 : (34 / 5) * (dG lam : ℝ) ^ 2 ≤ 200 * lam ^ 2 := by
    have hGle' : (dG lam : ℝ) ≤ 5 * lam + 1 := le_of_lt hGlt
    have hGnn : (0 : ℝ) ≤ (dG lam : ℝ) := le_of_lt hGpos
    have h5l1 : (0 : ℝ) ≤ 5 * lam + 1 := by linarith
    nlinarith [hGle', hGnn, h5l1, hlam, sq_nonneg (lam - 13 / 5)]
  have hnum3 : 13 * (dK lam : ℝ) ≤ 75 * lam := by
    have hKle : (dK lam : ℝ) ≤ 5 * lam + 2 := by linarith
    linarith
  have hnum4 : 13 * (dG lam : ℝ) ≤ 70 * lam := by
    have hGle' : (dG lam : ℝ) ≤ 5 * lam + 1 := le_of_lt hGlt
    linarith
  -- Exponent comparison: `r'/k ≥ 9` and `s'/g ≥ 34/5`.
  have hexp1 : (9 : ℝ) ≤ (dRp lam : ℝ) / (dK lam : ℝ) := by
    rw [le_div_iff₀ hKpos]
    have h1 : 9 * (dK lam : ℝ) ≤ 300 * lam ^ 2 / (dK lam : ℝ) := by
      rw [le_div_iff₀ hKpos]
      linarith [hnum1]
    linarith [h1, hrp]
  have hexp2 : (34 / 5 : ℝ) ≤ (dSp lam : ℝ) / (dG lam : ℝ) := by
    rw [le_div_iff₀ hGpos]
    have h1 : (34 / 5) * (dG lam : ℝ) ≤ 200 * lam ^ 2 / (dG lam : ℝ) := by
      rw [le_div_iff₀ hGpos]
      linarith [hnum2]
    linarith [h1, hsp]
  -- Coefficient comparison: `k²/2 ≤ (75/13)²λ²/2` and `g²/2 ≤ (70/13)²λ²/2`.
  have hcoef1 : (dK lam : ℝ) ^ 2 / 2 ≤ lam ^ 2 * (5625 / 338) := by
    have : (dK lam : ℝ) ^ 2 ≤ lam ^ 2 * (5625 / 169) := by nlinarith [hnum3]
    linarith
  have hcoef2 : (dG lam : ℝ) ^ 2 / 2 ≤ lam ^ 2 * (4900 / 338) := by
    have : (dG lam : ℝ) ^ 2 ≤ lam ^ 2 * (4900 / 169) := by nlinarith [hnum4]
    linarith
  -- The two Stechkin contributions.
  have ht1 : ((dK lam : ℝ) ^ 2 / 2) * (1 - 1 / (dK lam : ℝ)) ^ (dRp lam)
      ≤ lam ^ 2 * (5625 / 338) * Real.exp (-9) := by
    have h1 := one_sub_inv_pow_le_exp_neg (dK lam) (dRp lam) hK2
    have h2 : Real.exp (-((dRp lam : ℝ) / (dK lam : ℝ))) ≤ Real.exp (-9) := by
      apply Real.exp_le_exp.mpr; linarith [hexp1]
    have h3 : (1 - 1 / (dK lam : ℝ)) ^ (dRp lam) ≤ Real.exp (-9) := le_trans h1 h2
    have h4 : ((dK lam : ℝ) ^ 2 / 2) * (1 - 1 / (dK lam : ℝ)) ^ (dRp lam)
        ≤ ((dK lam : ℝ) ^ 2 / 2) * Real.exp (-9) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : ((dK lam : ℝ) ^ 2 / 2) * Real.exp (-9)
        ≤ lam ^ 2 * (5625 / 338) * Real.exp (-9) := by
      have := mul_le_mul_of_nonneg_right hcoef1 (Real.exp_pos (-9)).le
      linarith [this]
    linarith [h4, h5]
  have ht2 : ((dG lam : ℝ) ^ 2 / 2) * (1 - 1 / (dG lam : ℝ)) ^ (dSp lam)
      ≤ lam ^ 2 * (4900 / 338) * Real.exp (-(34 / 5)) := by
    have h1 := one_sub_inv_pow_le_exp_neg (dG lam) (dSp lam) hG2
    have h2 : Real.exp (-((dSp lam : ℝ) / (dG lam : ℝ))) ≤ Real.exp (-(34 / 5)) := by
      apply Real.exp_le_exp.mpr; linarith [hexp2]
    have h3 : (1 - 1 / (dG lam : ℝ)) ^ (dSp lam) ≤ Real.exp (-(34 / 5)) := le_trans h1 h2
    have h4 : ((dG lam : ℝ) ^ 2 / 2) * (1 - 1 / (dG lam : ℝ)) ^ (dSp lam)
        ≤ ((dG lam : ℝ) ^ 2 / 2) * Real.exp (-(34 / 5)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : ((dG lam : ℝ) ^ 2 / 2) * Real.exp (-(34 / 5))
        ≤ lam ^ 2 * (4900 / 338) * Real.exp (-(34 / 5)) := by
      have := mul_le_mul_of_nonneg_right hcoef2 (Real.exp_pos (-(34 / 5))).le
      linarith [this]
    linarith [h4, h5]
  -- The remaining numeric constant.
  have hkey : (5625 / 338 : ℝ) * Real.exp (-9) + (4900 / 338 : ℝ) * Real.exp (-(34 / 5)) ≤ 1 / 40 := by
    have h1 : (5625 / 338 : ℝ) * Real.exp (-9) ≤ (5625 / 338) * (1 / 7000) :=
      mul_le_mul_of_nonneg_left exp_neg_nine_le (by norm_num)
    have h2 : (4900 / 338 : ℝ) * Real.exp (-(34 / 5)) ≤ (4900 / 338) * (1 / 800) :=
      mul_le_mul_of_nonneg_left exp_neg_34_5_le (by norm_num)
    have h3 : (5625 / 338 : ℝ) * (1 / 7000) + (4900 / 338) * (1 / 800) ≤ 1 / 40 := by norm_num
    linarith [h1, h2, h3]
  rw [dDelta]
  have hsum : ((dK lam : ℝ) ^ 2 / 2) * (1 - 1 / (dK lam : ℝ)) ^ (dRp lam)
      + ((dG lam : ℝ) ^ 2 / 2) * (1 - 1 / (dG lam : ℝ)) ^ (dSp lam)
      ≤ lam ^ 2 * ((5625 / 338 : ℝ) * Real.exp (-9) + (4900 / 338 : ℝ) * Real.exp (-(34 / 5))) := by
    have h : lam ^ 2 * (5625 / 338 : ℝ) * Real.exp (-9)
          + lam ^ 2 * (4900 / 338 : ℝ) * Real.exp (-(34 / 5))
        = lam ^ 2 * ((5625 / 338 : ℝ) * Real.exp (-9) + (4900 / 338 : ℝ) * Real.exp (-(34 / 5))) := by
      ring
    linarith [ht1, ht2, h]
  have hfin : lam ^ 2 * ((5625 / 338 : ℝ) * Real.exp (-9) + (4900 / 338 : ℝ) * Real.exp (-(34 / 5)))
      ≤ lam ^ 2 * (1 / 40) := mul_le_mul_of_nonneg_left hkey (sq_nonneg lam)
  linarith [hsum, hfin, sq_nonneg lam]

end Work.BMF.liouville
