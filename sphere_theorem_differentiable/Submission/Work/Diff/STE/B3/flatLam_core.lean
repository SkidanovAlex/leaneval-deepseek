import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- **Core elementary estimate for the flat symbol difference.**

For `A, B ≥ 1` and any `w ≥ 0` with `|A - B| ≤ w`,

  `|(A² - 1)^k - (B² - 1)^k| ≤ 2 · k · 3^k · (1 + w)^{2k} · A^{k-1} · B^k`.

This is the abstract content of the pointwise symbol bound for the commutator `[Λ^k, M_c]` on the
flat torus: with `A = √(wt m)`, `B = √(wt n)` (so that `A² - 1 = Σ mᵢ²` and `λ(m) = (2π)²(Σ mᵢ²)`)
and `w = √(Σ (mᵢ - nᵢ)²)`, it converts the mean-value-type bound on powers into the weighted
estimate used in `flatLam_weighted_sub_le`.

Route: write `c = A² - 1`, `d = B² - 1`, `M = max A B`, `m = min A B`.

* `|c^k - d^k| ≤ k · |c - d| · (max c d)^{k-1}` (Mathlib's `abs_pow_sub_pow_le`);
* `|c - d| = |A - B| (A + B) ≤ 2 M w` and `max c d ≤ M²`, giving `≤ 2 k w M^{2k-1}`;
* `M ≤ m (1 + w)` since `M - m = |A - B| ≤ w` and `m ≥ 1`, and `(min)^{2k-1} ≤ A^{k-1} B^k`;
* finally `w (1 + w)^{2k-1} ≤ 3^k (1 + w)^{2k}` since `w ≤ 3^k (1 + w)`. -/
theorem flatLam_core
    (k : ℕ) (hk : 1 ≤ k) {A B w : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hw : 0 ≤ w) (hAB : |A - B| ≤ w) :
    |(A ^ 2 - 1) ^ k - (B ^ 2 - 1) ^ k|
      ≤ 2 * (k : ℝ) * 3 ^ k * (1 + w) ^ (2 * k) * A ^ (k - 1) * B ^ k := by
  have hA0 : 0 ≤ A := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hk0 : (0:ℝ) ≤ (k:ℝ) := by positivity
  have h1w : 0 ≤ 1 + w := by linarith
  have hM0 : 0 ≤ max A B := le_trans hA0 (le_max_left A B)
  have hm0 : 0 ≤ min A B := by have h := le_min hA hB; linarith
  have hc0 : 0 ≤ A ^ 2 - 1 := by nlinarith [hA]
  have hd0 : 0 ≤ B ^ 2 - 1 := by nlinarith [hB]
  have hmaxcd0 : 0 ≤ max (A^2-1) (B^2-1) := le_trans hc0 (le_max_left _ _)
  have hMw : (0:ℝ) ≤ 2 * max A B * w := by
    have : (0:ℝ) ≤ max A B * w := mul_nonneg hM0 hw
    linarith
  -- F1: the power-difference bound (mean value / geometric sum)
  have hpow : |(A ^ 2 - 1) ^ k - (B ^ 2 - 1) ^ k|
      ≤ (k : ℝ) * |(A ^ 2 - 1) - (B ^ 2 - 1)|
        * (max (A ^ 2 - 1) (B ^ 2 - 1)) ^ (k - 1) := by
    have h := abs_pow_sub_pow_le (A ^ 2 - 1) (B ^ 2 - 1) k
    rw [abs_of_nonneg hc0, abs_of_nonneg hd0] at h
    calc |(A ^ 2 - 1) ^ k - (B ^ 2 - 1) ^ k|
        ≤ |(A ^ 2 - 1) - (B ^ 2 - 1)| * (k:ℝ) * (max (A^2-1) (B^2-1))^(k-1) := h
      _ = (k:ℝ) * |(A^2-1) - (B^2-1)| * (max (A^2-1) (B^2-1))^(k-1) := by ring
  -- F2: `|c - d| ≤ 2 M w`
  have hsum0 : 0 ≤ A + B := by linarith
  have hABp : A + B ≤ 2 * max A B := by
    have h1 := le_max_left A B
    have h2 := le_max_right A B
    linarith
  have hcd : |(A^2-1) - (B^2-1)| ≤ 2 * max A B * w := by
    have heq : (A^2-1) - (B^2-1) = (A - B) * (A + B) := by ring
    rw [heq, abs_mul, abs_of_nonneg hsum0]
    calc |A - B| * (A + B) ≤ w * (2 * max A B) := mul_le_mul hAB hABp hsum0 hw
      _ = 2 * max A B * w := by ring
  -- F3: `max c d ≤ M²`
  have hmaxcd : max (A^2-1) (B^2-1) ≤ (max A B)^2 := by
    apply max_le
    · have : A^2 ≤ (max A B)^2 := pow_le_pow_left₀ hA0 (le_max_left A B) 2
      linarith
    · have : B^2 ≤ (max A B)^2 := pow_le_pow_left₀ hB0 (le_max_right A B) 2
      linarith
  -- F4: `M ≤ m (1 + w)`
  have hm1 : 1 ≤ min A B := le_min hA hB
  have hMm : max A B ≤ min A B * (1 + w) := by
    have hMsub : max A B - min A B ≤ w := by
      have := max_sub_min_eq_abs A B
      rw [this, abs_sub_comm]
      exact hAB
    have h1 : max A B ≤ min A B + w := by linarith
    have h2 : w ≤ min A B * w := by
      calc w = 1 * w := by ring
        _ ≤ min A B * w := mul_le_mul_of_nonneg_right hm1 hw
    calc max A B ≤ min A B + w := h1
      _ ≤ min A B + min A B * w := by linarith
      _ = min A B * (1 + w) := by ring
  -- F5: `(min A B)^{2k-1} ≤ A^{k-1} B^k`
  have hmm : (min A B) ^ (2*k-1) ≤ A ^ (k-1) * B ^ k := by
    have h1 : (min A B) ^ (k-1) ≤ A ^ (k-1) :=
      pow_le_pow_left₀ hm0 (min_le_left A B) (k-1)
    have h2 : (min A B) ^ k ≤ B ^ k := pow_le_pow_left₀ hm0 (min_le_right A B) k
    calc (min A B) ^ (2*k-1) = (min A B)^(k-1) * (min A B)^k := by
          rw [← show k - 1 + k = 2*k-1 by omega, pow_add]
      _ ≤ A^(k-1) * B^k := mul_le_mul h1 h2 (pow_nonneg hm0 k) (pow_nonneg hA0 (k-1))
  -- F6: `w (1 + w)^{2k-1} ≤ 3^k (1 + w)^{2k}`
  have hwX : w * (1+w)^(2*k-1) ≤ 3^k * (1+w)^(2*k) := by
    have h3 : (1:ℝ) ≤ 3^k := one_le_pow₀ (by norm_num)
    have hwle : w ≤ 3^k * (1+w) := by
      have : (1:ℝ) + w ≤ 3^k * (1+w) := by
        calc (1:ℝ) + w = 1 * (1 + w) := by ring
          _ ≤ 3^k * (1+w) := mul_le_mul_of_nonneg_right h3 h1w
      linarith
    have hsplit : (1+w) * (1+w)^(2*k-1) = (1+w)^(2*k) := by
      rw [← pow_succ', show 2*k-1+1 = 2*k by omega]
    calc w * (1+w)^(2*k-1) ≤ (3^k*(1+w)) * (1+w)^(2*k-1) :=
            mul_le_mul_of_nonneg_right hwle (pow_nonneg h1w _)
      _ = 3^k * ((1+w)*(1+w)^(2*k-1)) := by ring
      _ = 3^k * (1+w)^(2*k) := by rw [hsplit]
  calc |(A^2-1)^k - (B^2-1)^k|
      ≤ (k:ℝ) * |(A^2-1)-(B^2-1)| * (max (A^2-1) (B^2-1))^(k-1) := hpow
    _ ≤ (k:ℝ) * (2 * max A B * w) * ((max A B)^2)^(k-1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcd hk0)
          (pow_le_pow_left₀ hmaxcd0 hmaxcd (k-1)) (pow_nonneg hmaxcd0 _)
          (mul_nonneg hk0 hMw)
    _ = (k:ℝ) * (2 * max A B * w) * (max A B)^(2*(k-1)) := by rw [← pow_mul]
    _ = 2*(k:ℝ)*w * (max A B)^(2*k-1) := by
        have hsucc : max A B * (max A B)^(2*(k-1)) = (max A B)^(2*k-1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [← hsucc]
        ring
    _ ≤ 2*(k:ℝ)*w * (min A B * (1+w))^(2*k-1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM0 hMm _) (by positivity)
    _ = 2*(k:ℝ)*w * (1+w)^(2*k-1) * (min A B)^(2*k-1) := by
        rw [mul_pow]; ring
    _ ≤ 2*(k:ℝ)*w * (1+w)^(2*k-1) * (A^(k-1) * B^k) :=
        mul_le_mul_of_nonneg_left hmm (by positivity)
    _ ≤ 2*(k:ℝ)*3^k*(1+w)^(2*k) * (A^(k-1) * B^k) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc 2*(k:ℝ)*w*(1+w)^(2*k-1) = 2*(k:ℝ)*(w*(1+w)^(2*k-1)) := by ring
          _ ≤ 2*(k:ℝ)*(3^k*(1+w)^(2*k)) := mul_le_mul_of_nonneg_left hwX (by positivity)
          _ = 2*(k:ℝ)*3^k*(1+w)^(2*k) := by ring
    _ = 2 * (k:ℝ) * 3^k * (1+w)^(2*k) * A^(k-1) * B^k := by ring

end Work.Diff.STE.B3
