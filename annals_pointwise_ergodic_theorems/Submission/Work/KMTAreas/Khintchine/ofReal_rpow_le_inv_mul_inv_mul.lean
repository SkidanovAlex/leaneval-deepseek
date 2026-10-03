import Mathlib

namespace Work.KMTAreas.Khintchine

/-- From `c * A ≤ (S / 2^n)^(1/p)`, `c > 0`, `p > 0`, `A, S ≥ 0`, conclude the
`ENNReal` inequality `ofReal (A^p) ≤ (ofReal (c^p))⁻¹ * (ofReal (2^n))⁻¹ * ofReal S`.

This is the rearrangement `A^p ≤ c^{-p} * 2^{-n} * S` of the hypothesis, transported
to `ℝ≥0∞`.  It is the elementary arithmetic step used to extract `A` from inside the
`p`-th root of `S`. -/
lemma ofReal_rpow_le_inv_mul_inv_mul {p c A S : ℝ} {n : ℕ}
    (hc : 0 < c) (hp : 0 < p) (hA : 0 ≤ A) (hS : 0 ≤ S)
    (h : c * A ≤ (S / (2 : ℝ) ^ n) ^ (1 / p)) :
    ENNReal.ofReal (A ^ p) ≤
      (ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ * ENNReal.ofReal S := by
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hcp : (0 : ℝ) < c ^ p := Real.rpow_pos_of_pos hc p
  have hSpow : 0 ≤ S / (2 : ℝ) ^ n := div_nonneg hS h2n.le
  -- the real rearrangement `A^p ≤ c^{-p} * 2^{-n} * S`
  have hreal : A ^ p ≤ (c ^ p)⁻¹ * ((2 : ℝ) ^ n)⁻¹ * S := by
    have h1 : (c * A) ^ p ≤ ((S / (2 : ℝ) ^ n) ^ (1 / p)) ^ p :=
      Real.rpow_le_rpow (mul_nonneg hc.le hA) h hp.le
    rw [Real.mul_rpow hc.le hA] at h1
    rw [← Real.rpow_mul hSpow (1 / p) p, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one] at h1
    have h2 : A ^ p * c ^ p ≤ S / (2 : ℝ) ^ n := by
      rw [mul_comm (A ^ p) (c ^ p)]; exact h1
    have h3 : A ^ p ≤ (S / (2 : ℝ) ^ n) / c ^ p := (le_div_iff₀ hcp).mpr h2
    calc A ^ p ≤ (S / (2 : ℝ) ^ n) / c ^ p := h3
      _ = (c ^ p)⁻¹ * ((2 : ℝ) ^ n)⁻¹ * S := by field_simp
  -- transport to `ℝ≥0∞`, absorbing the inverses into `ofReal`
  rw [← ENNReal.ofReal_inv_of_pos hcp, ← ENNReal.ofReal_inv_of_pos h2n]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hcp.le),
      ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hcp.le) (inv_nonneg.mpr h2n.le))]
  exact ENNReal.ofReal_le_ofReal hreal

end Work.KMTAreas.Khintchine
