import Mathlib
import Submission.Work.BW.bpOddDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Pair bound for the denominator factors: when `|k|·|l| ≤ R²` and `η ≤ |l|`, the product of the
two factors for `k` and `−k` is at most `R⁴ + 2R²|k|η`. -/
lemma bpD_pair_mul_le {R η : ℝ} {l k : ℤ} (hη : 0 ≤ η) (hR : 0 < R)
    (hkl : |(k:ℝ)| * |(l:ℝ)| ≤ R^2) (hlη : η ≤ |(l:ℝ)|) :
    bpD R η l k * bpD R η l (-k) ≤ R^4 + 2 * R^2 * |(k:ℝ)| * η := by
  -- Write `a = |k|`, `b = |l|`, `t = k·l`.  The hypotheses say `a·b ≤ R²` and `η ≤ b`.
  set a := |(k:ℝ)| with ha
  set b := |(l:ℝ)| with hb
  set t := (k:ℝ) * (l:ℝ) with ht
  have hab : a * b ≤ R^2 := hkl
  have hlη' : η ≤ b := hlη
  have hR2 : 0 < R^2 := pow_pos hR 2
  -- `|t| = a·b ≤ R²`, hence both `R² ± t` are nonnegative and the absolute values unfold.
  have htab : |t| = a * b := by rw [ht, ha, hb, abs_mul]
  have htle : |t| ≤ R^2 := by rw [htab]; exact hab
  have h1 : 0 ≤ R^2 - t := by
    have h := le_abs_self t
    linarith
  have h2 : 0 ≤ R^2 + t := by
    have h := neg_abs_le t
    linarith
  have hD1 : bpD R η l k = (R^2 - t) + a * η := by
    unfold bpD
    rw [← ht, ← ha, abs_of_nonneg h1]
  have hD2 : bpD R η l (-k) = (R^2 + t) + a * η := by
    unfold bpD
    rw [Int.cast_neg, neg_mul, ← ht, abs_neg, ← ha, sub_neg_eq_add, abs_of_nonneg h2]
  rw [hD1, hD2]
  -- The product is `(R² + aη)² - t²`, and `a²η² ≤ t²` because `η ≤ b` and `|t| = a·b`.
  have ht2 : t^2 = a^2 * b^2 := by rw [← sq_abs t, htab]; ring
  have hη2 : η^2 ≤ b^2 := by
    have h3 : 0 ≤ b - η := by linarith
    have h4 : 0 ≤ b + η := by linarith
    nlinarith [mul_nonneg h3 h4]
  have haη : a^2 * η^2 ≤ t^2 := by
    rw [ht2]
    exact mul_le_mul_of_nonneg_left hη2 (sq_nonneg a)
  have hprod : ((R^2 - t) + a*η) * ((R^2 + t) + a*η) = (R^2 + a*η)^2 - t^2 := by ring
  rw [hprod]
  nlinarith [haη]

end Work.BW
