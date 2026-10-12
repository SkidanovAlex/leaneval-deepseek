import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB6Est.GFun
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open Work.BoseB6Est (gFun)

/-- **The exact `b`-increment of `gFun` at a general `τ > 0`.**  With
`σ = √(τ²+2τb)` and `σ' = √(τ²+2τb')`,

  `gFun τ b r − gFun τ b' r = (b−b')·(1 − 2τ/(σ+σ') − (b+b')/(2r²))`.

Indeed `gFun τ b r = τ + b − σ − b²/(2r²)`, and `σ − σ' = (σ² − σ'²)/(σ+σ')
= 2τ(b−b')/(σ+σ')`. -/
lemma gFun_beta_increment_gen {τ b b' r : ℝ} (hτ : 0 < τ) (hb : 0 ≤ b) (hb' : 0 ≤ b') :
    gFun τ b r - gFun τ b' r
      = (b - b') * (1 - 2 * τ / (Real.sqrt (τ ^ 2 + 2 * τ * b) + Real.sqrt (τ ^ 2 + 2 * τ * b'))
          - (b + b') / (2 * r ^ 2)) := by
  have hτ0 : 0 ≤ τ := le_of_lt hτ
  have hA : 0 ≤ τ ^ 2 + 2 * τ * b := by
    nlinarith [sq_nonneg τ, mul_nonneg hτ0 hb]
  have hA' : 0 ≤ τ ^ 2 + 2 * τ * b' := by
    nlinarith [sq_nonneg τ, mul_nonneg hτ0 hb']
  have hApos : 0 < τ ^ 2 + 2 * τ * b := by
    have h1 : 0 < τ * τ := mul_pos hτ hτ
    nlinarith [h1, mul_nonneg hτ0 hb]
  have hA'pos : 0 < τ ^ 2 + 2 * τ * b' := by
    have h1 : 0 < τ * τ := mul_pos hτ hτ
    nlinarith [h1, mul_nonneg hτ0 hb']
  set s := Real.sqrt (τ ^ 2 + 2 * τ * b) with hs
  set s' := Real.sqrt (τ ^ 2 + 2 * τ * b') with hs'
  have hs2 : s ^ 2 = τ ^ 2 + 2 * τ * b := by rw [hs, Real.sq_sqrt hA]
  have hs2' : s' ^ 2 = τ ^ 2 + 2 * τ * b' := by rw [hs', Real.sq_sqrt hA']
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hApos
  have hs'pos : 0 < s' := by rw [hs']; exact Real.sqrt_pos.mpr hA'pos
  have hsum : s + s' ≠ 0 := by
    have : 0 < s + s' := by linarith
    exact ne_of_gt this
  have hkey : (s - s') * (s + s') = 2 * τ * (b - b') := by nlinarith [hs2, hs2']
  have hdiff : s - s' = 2 * τ * (b - b') / (s + s') := by
    rw [eq_div_iff hsum]
    exact hkey
  have h1 : gFun τ b r = τ + b - s - b ^ 2 / (2 * r ^ 2) := by
    rw [gFun, show (τ + b) ^ 2 - b ^ 2 = τ ^ 2 + 2 * τ * b from by ring, ← hs]
  have h1' : gFun τ b' r = τ + b' - s' - b' ^ 2 / (2 * r ^ 2) := by
    rw [gFun, show (τ + b') ^ 2 - b' ^ 2 = τ ^ 2 + 2 * τ * b' from by ring, ← hs']
  rw [h1, h1']
  have step1 : τ + b - s - b ^ 2 / (2 * r ^ 2) - (τ + b' - s' - b' ^ 2 / (2 * r ^ 2))
      = (b - b') - (s - s') - (b ^ 2 - b' ^ 2) / (2 * r ^ 2) := by ring
  rw [step1, hdiff]
  ring

/-- The exact increment, together with `σ, σ' ≥ τ` and `σ + σ' > 0`, bounds the
bracket of `gFun_beta_increment_gen` by `1 + (b+b')/(2r²)` in absolute value. -/
lemma gFun_beta_diff_abs_le_aux {τ b b' r : ℝ} (hτ : 0 < τ) (hb : 0 ≤ b) (hb' : 0 ≤ b') :
    |gFun τ b r - gFun τ b' r| ≤ |b - b'| * (1 + (b + b') / (2 * r ^ 2)) := by
  have hτ0 : 0 ≤ τ := le_of_lt hτ
  have hA : 0 ≤ τ ^ 2 + 2 * τ * b := by
    nlinarith [sq_nonneg τ, mul_nonneg hτ0 hb]
  have hA' : 0 ≤ τ ^ 2 + 2 * τ * b' := by
    nlinarith [sq_nonneg τ, mul_nonneg hτ0 hb']
  set s := Real.sqrt (τ ^ 2 + 2 * τ * b) with hs
  set s' := Real.sqrt (τ ^ 2 + 2 * τ * b') with hs'
  have hs_ge : τ ≤ s := by
    rw [hs, Real.le_sqrt hτ0 hA]
    nlinarith [mul_nonneg hτ0 hb]
  have hs'_ge : τ ≤ s' := by
    rw [hs', Real.le_sqrt hτ0 hA']
    nlinarith [mul_nonneg hτ0 hb']
  have hsum_pos : 0 < s + s' := by linarith
  have hdiv_le : 2 * τ / (s + s') ≤ 1 := by
    rw [div_le_one hsum_pos]
    linarith
  have hdiv_nn : 0 ≤ 2 * τ / (s + s') := div_nonneg (by linarith) (le_of_lt hsum_pos)
  have hc_nn : 0 ≤ (b + b') / (2 * r ^ 2) := div_nonneg (by linarith) (by positivity)
  have hKabs : |1 - 2 * τ / (s + s') - (b + b') / (2 * r ^ 2)|
      ≤ 1 + (b + b') / (2 * r ^ 2) := by
    rw [abs_le]
    constructor <;> linarith
  have hmain := gFun_beta_increment_gen (τ := τ) (b := b) (b' := b') (r := r) hτ hb hb'
  rw [hmain, abs_mul]
  exact mul_le_mul_of_nonneg_left hKabs (abs_nonneg _)

/-- The exact `b`-increment of `gFun`: with `σ = √(τ²+2τb)`, `σ' = √(τ²+2τb')`,
`gFun τ b r − gFun τ b' r = (b−b')·(1 − 2τ/(σ+σ') − (b+b')/(2r²))`; since `σ+σ' ≥ 2τ` and
`σ − τ ≤ b`, `σ' − τ ≤ b'`, the bracket is in `[−(b+b')/(2r²), 1]` and in absolute value at
most `1 + (b+b')/(2r²)`. -/
theorem gFun_beta_diff_abs_le {τ b b' r : ℝ} (hτ : 0 < τ) (hτr : τ ≤ r ^ 2)
    (hb : 0 ≤ b) (hb' : 0 ≤ b') :
    |Work.BoseB6Est.gFun τ b r - Work.BoseB6Est.gFun τ b' r|
      ≤ |b - b'| * (1 + (b + b') / (2 * r ^ 2)) :=
  gFun_beta_diff_abs_le_aux hτ hb hb'

end Work.BoseBogFS
