import Mathlib

namespace Work.HP.BCS

/-- Growth-of-layer bound: for `k ≥ 1`, `k ≤ N`, `T ≥ 1`, `0 ≤ Y ≤ T`, `0 ≤ R ≤ C₀ Y`
(with `0 ≤ C₀`), `0 ≤ A ≤ B` and `0 < d`, the `k`-th layer quantity
`A (T+R)^{k-1} R / d` is bounded by `B (1+C₀)^N C₀ T^k (Y/T) / d`.

The proof is the chain
`T + R ≤ (1+C₀) T`, so `(T+R)^{k-1} ≤ (1+C₀)^{k-1} T^{k-1} ≤ (1+C₀)^N T^{k-1}`,
combined with `R ≤ C₀ Y` and `A ≤ B`, together with `T^k (Y/T) = T^{k-1} Y`. -/
theorem layer_grow_le {k N : ℕ} {A B C₀ T Y R d : ℝ}
    (hk : 1 ≤ k) (hkN : k ≤ N) (hT : 1 ≤ T) (hY : 0 ≤ Y) (hYT : Y ≤ T)
    (hR : 0 ≤ R) (hRC : R ≤ C₀ * Y) (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A) (hAB : A ≤ B)
    (hd : 0 < d) :
    A * (T + R) ^ (k - 1) * R / d ≤ B * (1 + C₀) ^ N * C₀ * T ^ k / d * (Y / T) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTne : T ≠ 0 := ne_of_gt hTpos
  have hB : 0 ≤ B := le_trans hA hAB
  have hC1 : (1 : ℝ) ≤ 1 + C₀ := by linarith
  have hTRle : T + R ≤ (1 + C₀) * T := by
    have : R ≤ C₀ * T := le_trans hRC (mul_le_mul_of_nonneg_left hYT hC₀)
    nlinarith
  have hTRnn : 0 ≤ T + R := by linarith
  -- `T^k (Y/T) = T^{k-1} Y`
  have hTk : T ^ k * (Y / T) = T ^ (k - 1) * Y := by
    have hk1 : k = k - 1 + 1 :=
      (Nat.succ_pred_eq_of_pos (lt_of_lt_of_le Nat.zero_lt_one hk)).symm
    conv_lhs => rw [hk1, pow_succ]
    rw [mul_assoc, mul_div_cancel₀ Y hTne]
  -- the power comparison
  have hpow1 : (T + R) ^ (k - 1) ≤ (1 + C₀) ^ N * T ^ (k - 1) := by
    have h1 : (T + R) ^ (k - 1) ≤ ((1 + C₀) * T) ^ (k - 1) :=
      pow_le_pow_left₀ hTRnn hTRle (k - 1)
    rw [mul_pow] at h1
    have h3 : (1 + C₀) ^ (k - 1) ≤ (1 + C₀) ^ N :=
      pow_le_pow_right₀ hC1 (le_trans (Nat.sub_le k 1) hkN)
    exact le_trans h1 (mul_le_mul_of_nonneg_right h3 (pow_nonneg hTpos.le _))
  have h1 : A * (T + R) ^ (k - 1) ≤ B * ((1 + C₀) ^ N * T ^ (k - 1)) :=
    mul_le_mul hAB hpow1 (pow_nonneg hTRnn _) hB
  have h2 : A * (T + R) ^ (k - 1) * R
      ≤ B * ((1 + C₀) ^ N * T ^ (k - 1)) * (C₀ * Y) :=
    mul_le_mul h1 hRC hR
      (mul_nonneg hB
        (mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + C₀) _) (pow_nonneg hTpos.le _)))
  have heq : B * ((1 + C₀) ^ N * T ^ (k - 1)) * (C₀ * Y)
      = B * (1 + C₀) ^ N * C₀ * T ^ (k - 1) * Y := by ring
  rw [heq] at h2
  have hdiv := div_le_div_of_nonneg_right h2 hd.le
  refine le_trans hdiv ?_
  have hfin : B * (1 + C₀) ^ N * C₀ * T ^ k / d * (Y / T)
      = B * (1 + C₀) ^ N * C₀ * T ^ (k - 1) * Y / d := by
    have hstep : B * (1 + C₀) ^ N * C₀ * T ^ k / d * (Y / T)
        = B * (1 + C₀) ^ N * C₀ * (T ^ k * (Y / T)) / d := by ring
    rw [hstep, hTk]
    ring
  exact le_of_eq hfin.symm

end Work.HP.BCS
