import Mathlib

/-!
# From the "gap" hypothesis to the diagonal hypothesis

This is a pure real-arithmetic bookkeeping lemma.  Given

* `γ ^ Kp * M < 2 * Cp`  (the "gap" hypothesis: the gap `γ ^ Kp` beats `M` against `Cp`),
* `2 ^ (m - 1) + m * (Kp - 1) ≤ K` (so that the exponent `K - 2 ^ (m-1)` is at least
  `m * (Kp - 1)`), and
* the constant comparison `4 * (2 * Cp) ^ m / (1000 * ((m : ℝ) + 1)) ^ m ≤ 1000 ^ (K - 2 ^ (m-1))`,

one deduces the diagonal bound

`(γ * M / (1000 * (m + 1))) ^ m ≤ (1/4) * (1000 / γ) ^ (K - 2 ^ (m-1))`.

The `γ ^ Kp` factor on `M` is traded against the `(1000 / γ) ^ (K - 2 ^ (m-1))` factor on the
right: raising `γ ^ Kp * M ≤ 2 * Cp` to the `m`-th power and using `Kp * m = m * (Kp - 1) + m`
gives `γ ^ m * M ^ m ≤ (2 * Cp) ^ m * (γ⁻¹) ^ (m * (Kp - 1))`, and since
`m * (Kp - 1) ≤ K - 2 ^ (m-1)` and `1 ≤ γ⁻¹`, the inverse powers are dominated by
`(γ⁻¹) ^ (K - 2 ^ (m-1))`.
-/

namespace Work.Peluse.PET

theorem diagHyp_of_gapHyp {m : ℕ} (hm : 2 ≤ m) {Kp K : ℕ} (hKp : 1 ≤ Kp)
    {Cp γ M : ℝ} (hCp : 0 < Cp) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 < M)
    (hgap : γ ^ Kp * M < 2 * Cp)
    (hKl : 2 ^ (m - 1) + m * (Kp - 1) ≤ K)
    (hKc : 4 * (2 * Cp) ^ m / (1000 * ((m : ℝ) + 1)) ^ m ≤ (1000 : ℝ) ^ (K - 2 ^ (m - 1))) :
    (γ * M / (1000 * ((m : ℝ) + 1))) ^ m ≤ (1 / 4) * (1000 / γ) ^ (K - 2 ^ (m - 1)) := by
  have hγne : γ ≠ 0 := ne_of_gt hγ
  have hγnn : 0 ≤ γ := le_of_lt hγ
  have hMnn : 0 ≤ M := le_of_lt hM
  -- (A) raise the gap inequality to the `m`-th power
  have hA1 : γ ^ Kp * M ≤ 2 * Cp := le_of_lt hgap
  have hA2 : (γ ^ Kp * M) ^ m ≤ (2 * Cp) ^ m :=
    pow_le_pow_left₀ (mul_nonneg (pow_nonneg hγnn Kp) hMnn) hA1 m
  have hA3 : γ ^ (Kp * m) * M ^ m ≤ (2 * Cp) ^ m := by
    calc γ ^ (Kp * m) * M ^ m = (γ ^ Kp * M) ^ m := by rw [mul_pow, ← pow_mul]
      _ ≤ (2 * Cp) ^ m := hA2
  have hKpm : Kp * m = m * (Kp - 1) + m := by
    conv_lhs => rw [show Kp = (Kp - 1) + 1 from by omega]
    rw [add_mul, one_mul]
    ring
  have hA4 : γ ^ (m * (Kp - 1)) * γ ^ m * M ^ m ≤ (2 * Cp) ^ m := by
    rw [hKpm, pow_add] at hA3
    exact hA3
  -- (B) trade the extra `γ ^ (m * (Kp - 1))` for inverse powers
  have hmul1 : γ ^ (m * (Kp - 1)) * (γ⁻¹) ^ (m * (Kp - 1)) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hγne, one_pow]
  have hgnn : 0 ≤ (γ⁻¹) ^ (m * (Kp - 1)) := pow_nonneg (inv_nonneg.mpr hγnn) _
  have hB : γ ^ m * M ^ m ≤ (2 * Cp) ^ m * (γ⁻¹) ^ (m * (Kp - 1)) := by
    calc γ ^ m * M ^ m
        = γ ^ m * M ^ m * (γ ^ (m * (Kp - 1)) * (γ⁻¹) ^ (m * (Kp - 1))) := by
            rw [hmul1, mul_one]
      _ = (γ ^ (m * (Kp - 1)) * γ ^ m * M ^ m) * (γ⁻¹) ^ (m * (Kp - 1)) := by ring
      _ ≤ (2 * Cp) ^ m * (γ⁻¹) ^ (m * (Kp - 1)) :=
            mul_le_mul_of_nonneg_right hA4 hgnn
  -- (C) the elementary constant/geometric comparisons
  have hDpos : (0:ℝ) < (1000 * ((m : ℝ) + 1)) ^ m := by positivity
  have hKss : m * (Kp - 1) ≤ K - 2 ^ (m - 1) := by
    apply Nat.le_sub_of_add_le
    rw [Nat.add_comm]
    exact hKl
  have hg1 : 1 ≤ γ⁻¹ := (one_le_inv₀ hγ).mpr hγ1
  have hKc' : 4 * ((2 * Cp) ^ m / (1000 * ((m : ℝ) + 1)) ^ m)
      ≤ (1000 : ℝ) ^ (K - 2 ^ (m - 1)) := by
    have h := hKc
    rw [mul_div_assoc] at h
    exact h
  have hC1 : (2 * Cp) ^ m / (1000 * ((m : ℝ) + 1)) ^ m
      ≤ (1 / 4) * (1000 : ℝ) ^ (K - 2 ^ (m - 1)) := by
    have hY : (2 * Cp) ^ m / (1000 * ((m : ℝ) + 1)) ^ m
        ≤ (1000 : ℝ) ^ (K - 2 ^ (m - 1)) / 4 := by
      rw [le_div_iff₀ (show (0:ℝ) < 4 by norm_num)]
      linarith [hKc']
    have e : (1000 : ℝ) ^ (K - 2 ^ (m - 1)) / 4
        = (1 / 4) * (1000 : ℝ) ^ (K - 2 ^ (m - 1)) := by ring
    rwa [e] at hY
  have hC2 : (2 * Cp) ^ m / (1000 * ((m : ℝ) + 1)) ^ m * (γ⁻¹) ^ (m * (Kp - 1))
      ≤ (1 / 4) * (1000 : ℝ) ^ (K - 2 ^ (m - 1)) * (γ⁻¹) ^ (m * (Kp - 1)) :=
    mul_le_mul_of_nonneg_right hC1 hgnn
  have hdivpow : (1000 / γ) ^ (K - 2 ^ (m - 1))
      = (1000 : ℝ) ^ (K - 2 ^ (m - 1)) * (γ⁻¹) ^ (K - 2 ^ (m - 1)) := by
    rw [div_eq_mul_inv, mul_pow]
  have hC3 : (1 / 4) * (1000 : ℝ) ^ (K - 2 ^ (m - 1)) * (γ⁻¹) ^ (m * (Kp - 1))
      ≤ (1 / 4) * (1000 / γ) ^ (K - 2 ^ (m - 1)) := by
    have hpow : (γ⁻¹) ^ (m * (Kp - 1)) ≤ (γ⁻¹) ^ (K - 2 ^ (m - 1)) :=
      pow_le_pow_right₀ hg1 hKss
    have hcoef : (0:ℝ) ≤ (1 / 4) * (1000 : ℝ) ^ (K - 2 ^ (m - 1)) := by positivity
    calc (1 / 4) * (1000 : ℝ) ^ (K - 2 ^ (m - 1)) * (γ⁻¹) ^ (m * (Kp - 1))
        ≤ (1 / 4) * (1000 : ℝ) ^ (K - 2 ^ (m - 1)) * (γ⁻¹) ^ (K - 2 ^ (m - 1)) :=
            mul_le_mul_of_nonneg_left hpow hcoef
      _ = (1 / 4) * (1000 / γ) ^ (K - 2 ^ (m - 1)) := by
            rw [hdivpow]; ring
  -- (D) assemble
  have hL : (γ * M / (1000 * ((m : ℝ) + 1))) ^ m
      = (γ ^ m * M ^ m) / (1000 * ((m : ℝ) + 1)) ^ m := by
    rw [div_pow, mul_pow]
  calc (γ * M / (1000 * ((m : ℝ) + 1))) ^ m
      = (γ ^ m * M ^ m) / (1000 * ((m : ℝ) + 1)) ^ m := hL
    _ ≤ (2 * Cp) ^ m * (γ⁻¹) ^ (m * (Kp - 1)) / (1000 * ((m : ℝ) + 1)) ^ m :=
          div_le_div_of_nonneg_right hB (le_of_lt hDpos)
    _ = (2 * Cp) ^ m / (1000 * ((m : ℝ) + 1)) ^ m * (γ⁻¹) ^ (m * (Kp - 1)) := by ring
    _ ≤ (1 / 4) * (1000 : ℝ) ^ (K - 2 ^ (m - 1)) * (γ⁻¹) ^ (m * (Kp - 1)) := hC2
    _ ≤ (1 / 4) * (1000 / γ) ^ (K - 2 ^ (m - 1)) := hC3

end Work.Peluse.PET
