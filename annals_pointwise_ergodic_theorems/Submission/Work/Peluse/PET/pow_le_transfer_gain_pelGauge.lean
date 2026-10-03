import Mathlib

namespace Work.Peluse.PET

/-- Pure real-arithmetic bookkeeping for the régime (B) of
`Work.Peluse.PET.boxNormPow_control_linear_v2`: the transfer-up gain at the *fine* gauge.

The hypotheses are
* `hKe` — the target exponent `K` dominates the fine exponent `K1` plus the transfer gain
  `eT·(2^m − 1)`,
* `hKh` — `1000^K` absorbs the constant `1000^K1·(1 + a^{-eT})/cT`, and
* `hratio` — the ratio `H1/H` is at least the gauge `a·γ^(2^m−1)`.

The conclusion is the "transferred" bound `(γ/1000)^K ≤ cT·(H1/H)^eT·(γ/1000)^K1`.

The mechanism: `hKh` gives `1 + a^{-eT} ≤ cT·1000^(K−K1)`, hence after multiplying by `a^eT`
the single key inequality `1 ≤ cT·a^eT·1000^(K−K1)`.  Splitting `(γ/1000)^(K−K1) =
(γ/1000)^K1·... ` and using `γ^(K−K1) ≤ γ^(eT(2^m−1))` (as `0 < γ ≤ 1`), together with
`1/1000^(K−K1) ≤ cT·a^eT`, converts the `1000`-loss into the gauge gain `(a·γ^(2^m−1))^eT`,
which `hratio` then dominates by `(H1/H)^eT`. -/
theorem pow_le_transfer_gain_pelGauge {m : ℕ} (hm : 0 < m) {K1 K : ℕ} (hK1 : 1 ≤ K1) {eT : ℕ}
    {cT a γ H1 H : ℝ} (hcT : 0 < cT) (ha : 0 < a) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hH : 0 < H) (hH1 : 0 < H1) (hKe : K1 + eT * (2 ^ m - 1) ≤ K)
    (hKh : 1000 ^ K1 * (1 + (1 / a) ^ eT) / cT ≤ (1000 : ℝ) ^ K)
    (hratio : a * γ ^ (2 ^ m - 1) ≤ H1 / H) :
    (γ / 1000) ^ K ≤ cT * (H1 / H) ^ eT * (γ / 1000) ^ K1 := by
  have hK1K : K1 ≤ K := le_trans (Nat.le_add_right K1 (eT * (2 ^ m - 1))) hKe
  have hKe' : eT * (2 ^ m - 1) + K1 ≤ K := by omega
  have hD : eT * (2 ^ m - 1) ≤ K - K1 := Nat.le_sub_of_add_le hKe'
  -- (1) `hKh` clears the denominators and the factor `1000^K1`.
  have h1 : 1000 ^ K1 * (1 + (1 / a) ^ eT) ≤ (1000 : ℝ) ^ K * cT :=
    (div_le_iff₀ hcT).mp hKh
  have h2 : (1000 : ℝ) ^ K = 1000 ^ K1 * 1000 ^ (K - K1) := by
    rw [← pow_add, Nat.add_sub_of_le hK1K]
  have hpk : 1000 ^ K1 * (1 + (1 / a) ^ eT) ≤ 1000 ^ K1 * (cT * 1000 ^ (K - K1)) := by
    calc 1000 ^ K1 * (1 + (1 / a) ^ eT) ≤ (1000 : ℝ) ^ K * cT := h1
      _ = 1000 ^ K1 * (cT * 1000 ^ (K - K1)) := by rw [h2]; ring
  have hA : 1 + (1 / a) ^ eT ≤ cT * 1000 ^ (K - K1) :=
    le_of_mul_le_mul_left hpk (by positivity)
  -- (2) the key scalar inequality `1 ≤ cT·a^eT·1000^(K−K1)`.
  have hae : a ^ eT * (1 / a) ^ eT = 1 := by
    rw [← mul_pow, mul_one_div, div_self (ne_of_gt ha), one_pow]
  have haeT : (0 : ℝ) ≤ a ^ eT := by positivity
  have hkey : 1 ≤ cT * a ^ eT * 1000 ^ (K - K1) := by
    have hmul := mul_le_mul_of_nonneg_left hA haeT
    have h1' : a ^ eT * (1 + (1 / a) ^ eT) = 1 + a ^ eT := by
      rw [mul_add, mul_one, hae, add_comm]
    have : (1 : ℝ) ≤ a ^ eT * (cT * 1000 ^ (K - K1)) := by
      rw [h1'] at hmul; linarith [hmul, haeT]
    calc (1 : ℝ) ≤ a ^ eT * (cT * 1000 ^ (K - K1)) := this
      _ = cT * a ^ eT * 1000 ^ (K - K1) := by ring
  -- (3) the exponential step at the fine scale, with the `1000`-loss turned into the gain.
  have hbpow : (a * γ ^ (2 ^ m - 1)) ^ eT = a ^ eT * γ ^ (eT * (2 ^ m - 1)) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm (2 ^ m - 1) eT]
  have hcore2 : 1 / (1000 : ℝ) ^ (K - K1) ≤ cT * a ^ eT :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 ^ (K - K1))).mpr hkey
  have hcore : (γ / 1000) ^ (K - K1) ≤ cT * (a * γ ^ (2 ^ m - 1)) ^ eT := by
    rw [hbpow]
    calc (γ / 1000) ^ (K - K1)
        = γ ^ (K - K1) / (1000 : ℝ) ^ (K - K1) := div_pow γ 1000 (K - K1)
      _ ≤ γ ^ (eT * (2 ^ m - 1)) / (1000 : ℝ) ^ (K - K1) :=
          div_le_div_of_nonneg_right (pow_le_pow_of_le_one hγ.le hγ1 hD) (by positivity)
      _ = γ ^ (eT * (2 ^ m - 1)) * (1 / (1000 : ℝ) ^ (K - K1)) := by ring
      _ ≤ γ ^ (eT * (2 ^ m - 1)) * (cT * a ^ eT) :=
          mul_le_mul_of_nonneg_left hcore2 (by positivity)
      _ = cT * (a ^ eT * γ ^ (eT * (2 ^ m - 1))) := by ring
  -- (4) `hratio` upgrades the gauge gain to `(H1/H)^eT`, and we multiply back by `(γ/1000)^K1`.
  have hfinal : (γ / 1000) ^ (K - K1) ≤ cT * (H1 / H) ^ eT :=
    le_trans hcore (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hratio eT) hcT.le)
  calc (γ / 1000) ^ K = (γ / 1000) ^ (K1 + (K - K1)) := by
        rw [Nat.add_sub_of_le hK1K]
    _ = (γ / 1000) ^ K1 * (γ / 1000) ^ (K - K1) := pow_add _ _ _
    _ ≤ (γ / 1000) ^ K1 * (cT * (H1 / H) ^ eT) :=
        mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = cT * (H1 / H) ^ eT * (γ / 1000) ^ K1 := by ring

end Work.Peluse.PET
