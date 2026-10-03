import Mathlib

namespace Work.KMTAreas.A4Z

/-- **The sharp gain.**  With `c ≥ 0`, `j ≥ c + 3`, `s ≥ 2^{d(l-1)}` and `A ≥ s (j - c - 2)`,
the reciprocal eighth power of `A` is bounded by the reciprocal of `(2^d (c+4))^8 2^{8dl} (1+j)^8`.

This is the bookkeeping inequality behind the `2^{-8ρ·}` gain of the `lip-2` tail chain: it says
that the gain obtained from `A ≥ s (j-c-2)` (with `s` at least the arithmetic separation
`2^{d(l-1)}`) is at least the product of `2^{-8dl}` with the decay `(1+j)^{-8}` coming from the
number `j` of levels, up to the constant `(2^d(c+4))^8`. -/
theorem sharpGain {d l : ℕ} {s c j A : ℝ} (hc : 0 ≤ c) (hj : c + 3 ≤ j)
    (hs : (2 : ℝ) ^ ((d : ℝ) * ((l : ℝ) - 1)) ≤ s) (hA : s * (j - c - 2) ≤ A) :
    A ^ (-(8 : ℝ)) ≤ (2 ^ d * (c + 4)) ^ 8 * (2 : ℝ) ^ (-(8 * (d : ℝ) * (l : ℝ)))
      * (1 + j) ^ (-(8 : ℝ)) := by
  have h2pos : (0:ℝ) < 2 := by norm_num
  have htpos : 0 < j - c - 2 := by linarith
  have hqpos : 0 < 1 + j := by linarith
  have hPpos : 0 < (2:ℝ) ^ ((d:ℝ) * ((l:ℝ) - 1)) := Real.rpow_pos_of_pos h2pos _
  have hspos : 0 < s := lt_of_lt_of_le hPpos hs
  have hApos : 0 < A := lt_of_lt_of_le (mul_pos hspos htpos) hA
  have hXpos : 0 < (2:ℝ)^(d*l) := by positivity
  -- `2 ^ {d(l-1)} = 2^{dl} / 2^d`
  have hPeq : (2:ℝ) ^ ((d:ℝ) * ((l:ℝ) - 1)) = (2:ℝ)^(d*l) / (2:ℝ)^d := by
    rw [← Real.rpow_natCast 2 (d*l), ← Real.rpow_natCast 2 d, ← Real.rpow_sub h2pos]
    congr 1
    push_cast
    ring
  have h2dP : (2:ℝ)^d * ((2:ℝ) ^ ((d:ℝ) * ((l:ℝ) - 1))) = (2:ℝ)^(d*l) := by
    rw [hPeq, mul_div_cancel₀ _ (by positivity : (2:ℝ)^d ≠ 0)]
  have hAPt : (2:ℝ) ^ ((d:ℝ) * ((l:ℝ) - 1)) * (j - c - 2) ≤ A :=
    le_trans (mul_le_mul_of_nonneg_right hs htpos.le) hA
  have harith : 1 + j ≤ (c + 4) * (j - c - 2) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c+3)
      (by linarith : (0:ℝ) ≤ j - c - 3)]
  -- `2^{dl} (1+j) ≤ A · 2^d (c+4)`
  have hcore : (2:ℝ)^(d*l) * (1+j) ≤ A * ((2:ℝ)^d * (c+4)) := by
    have h1 : (2:ℝ)^(d*l) * (j - c - 2) ≤ A * (2:ℝ)^d := by
      calc (2:ℝ)^(d*l) * (j - c - 2)
          = (2:ℝ)^d * ((2:ℝ) ^ ((d:ℝ) * ((l:ℝ) - 1)) * (j - c - 2)) := by
            rw [← h2dP, mul_assoc]
        _ ≤ (2:ℝ)^d * A := mul_le_mul_of_nonneg_left hAPt (by positivity)
        _ = A * (2:ℝ)^d := by ring
    calc (2:ℝ)^(d*l) * (1+j)
        ≤ (2:ℝ)^(d*l) * ((c+4) * (j - c - 2)) :=
          mul_le_mul_of_nonneg_left harith (by positivity)
      _ = ((2:ℝ)^(d*l) * (j - c - 2)) * (c + 4) := by ring
      _ ≤ (A * (2:ℝ)^d) * (c+4) := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = A * ((2:ℝ)^d * (c+4)) := by ring
  have hinv : A⁻¹ ≤ (2:ℝ)^d * (c+4) * ((2:ℝ)^(d*l))⁻¹ * (1+j)⁻¹ := by
    have hXq : 0 < (2:ℝ)^(d*l) * (1+j) := mul_pos hXpos hqpos
    have h1 : A⁻¹ ≤ (2:ℝ)^d * (c+4) / ((2:ℝ)^(d*l) * (1+j)) := by
      rw [le_div_iff₀ hXq]
      calc A⁻¹ * ((2:ℝ)^(d*l) * (1+j))
          ≤ A⁻¹ * (A * ((2:ℝ)^d * (c+4))) := mul_le_mul_of_nonneg_left hcore (by positivity)
        _ = (2:ℝ)^d * (c+4) := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hApos), one_mul]
    calc A⁻¹ ≤ (2:ℝ)^d * (c+4) / ((2:ℝ)^(d*l) * (1+j)) := h1
      _ = (2:ℝ)^d * (c+4) * ((2:ℝ)^(d*l))⁻¹ * (1+j)⁻¹ := by
          rw [div_eq_mul_inv, mul_inv]; ring
  have hA8 : A ^ (-(8:ℝ)) = (A⁻¹)^8 := by
    rw [Real.rpow_neg hApos.le]
    rw [show (8:ℝ) = ((8:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_pow]
  have hq8 : (1+j) ^ (-(8:ℝ)) = ((1+j)⁻¹)^8 := by
    rw [Real.rpow_neg hqpos.le]
    rw [show (8:ℝ) = ((8:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_pow]
  have hmid : (2:ℝ) ^ (-(8*(d:ℝ)*(l:ℝ))) = (((2:ℝ)^(d*l))⁻¹)^8 := by
    rw [show -(8*(d:ℝ)*(l:ℝ)) = -(((8*d*l : ℕ) : ℝ)) by push_cast; ring]
    rw [Real.rpow_neg_natCast, zpow_neg, zpow_natCast,
        show 8*d*l = (d*l)*8 by ring, pow_mul, inv_pow]
  have hR : (2 ^ d * (c+4))^8 * (2:ℝ)^(-(8*(d:ℝ)*(l:ℝ))) * (1+j)^(-(8:ℝ))
      = ((2:ℝ)^d * (c+4) * ((2:ℝ)^(d*l))⁻¹ * (1+j)⁻¹)^8 := by
    rw [hmid, hq8]
    ring
  calc A ^ (-(8:ℝ)) = (A⁻¹)^8 := hA8
    _ ≤ ((2:ℝ)^d * (c+4) * ((2:ℝ)^(d*l))⁻¹ * (1+j)⁻¹)^8 :=
        pow_le_pow_left₀ (by positivity) hinv 8
    _ = (2 ^ d * (c+4))^8 * (2:ℝ)^(-(8*(d:ℝ)*(l:ℝ))) * (1+j)^(-(8:ℝ)) := hR.symm

end Work.KMTAreas.A4Z
