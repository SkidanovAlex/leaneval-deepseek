import Mathlib

namespace Work.GM.S3

/-- Pure real arithmetic behind the tail bound for `ψ` in GM (7.1): with `L > 0`, `T ≥ 1`, `δ > 0`,
`Cj ≥ 0` and `K ≥ L·T^δ/2` (so `K > 0`), one has
`4·(Cj(2L)^j)·K/K^j ≤ 2^{2j+1}·Cj·L·T^{-δ(j-1)}` for `j ≥ 2`.
(Indeed `K^{j-1} ≥ (L T^δ/2)^{j-1}` and `(2L)^j/L^{j-1} = 2^j·L`; note `(T^δ)^{j-1} = T^{δ(j-1)}`.) -/
theorem psi_tail_arith (Cj L T K δ : ℝ) (j : ℕ) (hj : 2 ≤ j)
    (hCj : 0 ≤ Cj) (hL : 0 < L) (hT : 1 ≤ T) (hδ : 0 < δ) (hK : L * T ^ δ / 2 ≤ K) :
    (4 : ℝ) * (Cj * (2 * L) ^ j) * K / K ^ j
      ≤ 2 ^ (2 * j + 1) * Cj * L * T ^ (-(δ * ((j : ℝ) - 1))) := by
  have _hδ : 0 < δ := hδ
  have hT0 : (0 : ℝ) < T := by linarith
  have hTd : (0 : ℝ) < T ^ δ := Real.rpow_pos_of_pos hT0 δ
  have hbpos : (0 : ℝ) < L * T ^ δ / 2 := by positivity
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le hbpos hK
  have hj1 : 1 ≤ j := by omega
  -- The tail factor `K / K^j = 1 / K^{j-1}` is at most `(1/(L T^δ/2))^{j-1}`.
  have hstep1 : K / K ^ j ≤ (1 / (L * T ^ δ / 2)) ^ (j - 1) := by
    have hKpow : K / K ^ j = (K ^ (j - 1))⁻¹ := by
      conv_lhs => rw [show j = (j - 1) + 1 by omega]
      rw [pow_succ, div_eq_iff (by positivity), ← mul_assoc,
        inv_mul_cancel₀ (by positivity), one_mul]
    rw [hKpow, one_div_pow]
    have h := one_div_le_one_div_of_le (pow_pos hbpos (j - 1))
      (pow_le_pow_left₀ hbpos.le hK (j - 1))
    simpa [one_div] using h
  -- The remaining factor is an exact identity.
  have hEq : (4 : ℝ) * (Cj * (2 * L) ^ j) * (1 / (L * T ^ δ / 2)) ^ (j - 1)
      = 2 ^ (2 * j + 1) * Cj * L * T ^ (-(δ * ((j : ℝ) - 1))) := by
    have hrpow : T ^ (-(δ * ((j : ℝ) - 1))) = ((T ^ δ) ^ (j - 1))⁻¹ := by
      have hc : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
        rw [Nat.cast_sub hj1]; norm_num
      rw [← hc, Real.rpow_neg (le_of_lt hT0)]
      congr 1
      rw [← Real.rpow_natCast (T ^ δ) (j - 1)]
      rw [Real.rpow_mul (le_of_lt hT0)]
    rw [hrpow]
    have h2 : (2 : ℝ) ^ (2 * j + 1) = 4 * 2 ^ j * 2 ^ (j - 1) := by
      rw [show 2 * j + 1 = j + (j - 1) + 2 by omega]
      rw [pow_add, pow_add]
      ring
    have hLp : L ^ j = L ^ (j - 1) * L := by
      conv_lhs => rw [← Nat.sub_add_cancel hj1]
      rw [pow_succ]
    have hb_inv : (1 / (L * T ^ δ / 2)) ^ (j - 1)
        = 2 ^ (j - 1) * (L ^ (j - 1))⁻¹ * ((T ^ δ) ^ (j - 1))⁻¹ := by
      rw [one_div, inv_pow, div_pow, mul_pow]
      rw [inv_div]
      rw [div_eq_mul_inv, mul_inv]
      ring
    rw [hb_inv, mul_pow, hLp, h2]
    field_simp
  calc (4 : ℝ) * (Cj * (2 * L) ^ j) * K / K ^ j
      = 4 * (Cj * (2 * L) ^ j) * (K / K ^ j) := by rw [mul_div_assoc]
    _ ≤ 4 * (Cj * (2 * L) ^ j) * (1 / (L * T ^ δ / 2)) ^ (j - 1) :=
        mul_le_mul_of_nonneg_left hstep1 (by positivity)
    _ = 2 ^ (2 * j + 1) * Cj * L * T ^ (-(δ * ((j : ℝ) - 1))) := hEq

end Work.GM.S3
