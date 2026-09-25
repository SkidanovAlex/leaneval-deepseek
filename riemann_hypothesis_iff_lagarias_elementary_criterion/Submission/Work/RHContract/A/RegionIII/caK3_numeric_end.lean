import Mathlib

namespace Work.RHContract.A.RegionIII

/- Numeric end estimate for the region III `caK3` term: for `ξ ≥ 10^8`
the elementary upper bound for `caK3 ξ`,
`3 log((3.69 ξ)^{1/3}) + 10 + (11056/10000) (3.69 ξ)^{1/3} ((1/2) ξ^{-1/4} + 6 ξ^{-1/2})`,
is at most `(1/100) √ξ`.

The proof substitutes `u = ξ^{1/12}` (all fractional powers become integer powers
of `u`), uses `3.69^{1/3} ≤ 8/5`, `log u ≤ u` and `log(3.69^{1/3}) ≤ 8/5 - 1`, and
reduces everything to the polynomial inequality `13 u + 14 ≤ u^6 / 100` for `u ≥ 23/5`. -/
set_option maxHeartbeats 1000000 in
theorem caK3_numeric_end (ξ : ℝ) (hξ : (10 : ℝ) ^ 8 ≤ ξ) :
    3 * Real.log ((3.69 * ξ) ^ (1 / 3 : ℝ)) + 10
      + (11056 / 10000) * (3.69 * ξ) ^ (1 / 3 : ℝ)
          * ((1 / 2) * ξ ^ (-(1 / 4 : ℝ)) + 6 * ξ ^ (-(1 / 2 : ℝ)))
    ≤ (1 / 100) * Real.sqrt ξ := by
  have hξ0 : 0 < ξ := by norm_num at hξ ⊢; linarith
  set u : ℝ := ξ ^ (1 / 12 : ℝ) with hu
  have hu0 : 0 < u := by rw [hu]; exact Real.rpow_pos_of_pos hξ0 _
  have hu12 : u ^ 12 = ξ := by
    rw [hu]; rw [← Real.rpow_natCast]; rw [← Real.rpow_mul (le_of_lt hξ0)]; norm_num
  have h4u : (23 / 5 : ℝ) ≤ u := by
    have hpow : (23 / 5 : ℝ) ^ 12 ≤ u ^ 12 := by rw [hu12]; norm_num at hξ ⊢; linarith
    exact (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 23 / 5) (le_of_lt hu0)
      (by norm_num : (12 : ℕ) ≠ 0)).mp hpow
  have h13 : ξ ^ (1 / 3 : ℝ) = u ^ 4 := by
    rw [← Real.rpow_natCast u 4]; rw [hu]; rw [← Real.rpow_mul (le_of_lt hξ0)]; norm_num
  have h14 : ξ ^ (-(1 / 4) : ℝ) = (u ^ 3)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hξ0) (1 / 4 : ℝ)]; congr 1
    rw [← Real.rpow_natCast u 3]; rw [hu]; rw [← Real.rpow_mul (le_of_lt hξ0)]; norm_num
  have h12 : ξ ^ (-(1 / 2) : ℝ) = (u ^ 6)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hξ0) (1 / 2 : ℝ)]; congr 1
    rw [← Real.rpow_natCast u 6]; rw [hu]; rw [← Real.rpow_mul (le_of_lt hξ0)]; norm_num
  have h369 : (3.69 * ξ) ^ (1 / 3 : ℝ) = (3.69 : ℝ) ^ (1 / 3 : ℝ) * u ^ 4 := by
    rw [Real.mul_rpow (by norm_num) (le_of_lt hξ0)]; rw [h13]
  have hsqrt : Real.sqrt ξ = u ^ 6 := by
    rw [Real.sqrt_eq_rpow]; rw [← Real.rpow_natCast u 6]; rw [hu]
    rw [← Real.rpow_mul (le_of_lt hξ0)]; norm_num
  have h369le : (3.69 : ℝ) ^ (1 / 3 : ℝ) ≤ 8 / 5 := by
    have hbase : (3.69 : ℝ) ≤ (8 / 5 : ℝ) ^ 3 := by norm_num
    have hkey : ((8 / 5 : ℝ) ^ 3) ^ (1 / 3 : ℝ) = 8 / 5 := by
      have h1 : (8 / 5 : ℝ) ^ 3 = (8 / 5 : ℝ) ^ (3 : ℝ) := (Real.rpow_natCast (8 / 5 : ℝ) 3).symm
      rw [h1, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8 / 5) (3 : ℝ) (1 / 3 : ℝ)]
      norm_num
    calc (3.69 : ℝ) ^ (1 / 3 : ℝ) ≤ ((8 / 5 : ℝ) ^ 3) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hbase (by norm_num)
      _ = 8 / 5 := hkey
  rw [h369, h14, h12, hsqrt]
  -- Now all fractional powers are integer powers of `u`.
  have hterm1 : 3 * Real.log ((3.69 : ℝ) ^ (1 / 3 : ℝ) * u ^ 4) ≤ 12 * u + 2 := by
    have h369pos : 0 < (3.69 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have hlogmul : Real.log ((3.69 : ℝ) ^ (1 / 3 : ℝ) * u ^ 4)
        = Real.log ((3.69 : ℝ) ^ (1 / 3 : ℝ)) + Real.log (u ^ 4) :=
      Real.log_mul (ne_of_gt h369pos) (pow_ne_zero 4 (ne_of_gt hu0))
    rw [hlogmul, Real.log_pow u 4]
    have hb1 : Real.log ((3.69 : ℝ) ^ (1 / 3 : ℝ)) ≤ (8 / 5 : ℝ) - 1 :=
      le_trans (Real.log_le_sub_one_of_pos h369pos) (by linarith)
    have hb2 : Real.log u ≤ u := le_trans (Real.log_le_sub_one_of_pos hu0) (by linarith)
    linarith [hb1, hb2]
  have hterm3 :
      (11056 / 10000) * ((3.69 : ℝ) ^ (1 / 3 : ℝ) * u ^ 4)
          * ((1 / 2) * (u ^ 3)⁻¹ + 6 * (u ^ 6)⁻¹) ≤ u + 1 := by
    have hBnn : 0 ≤ (1 / 2) * (u ^ 3)⁻¹ + 6 * (u ^ 6)⁻¹ := by positivity
    have hA : (11056 / 10000) * ((3.69 : ℝ) ^ (1 / 3 : ℝ) * u ^ 4)
        ≤ (11056 / 10000) * ((8 / 5) * u ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact mul_le_mul_of_nonneg_right h369le (by positivity)
    have hstep :
        (11056 / 10000) * ((3.69 : ℝ) ^ (1 / 3 : ℝ) * u ^ 4)
            * ((1 / 2) * (u ^ 3)⁻¹ + 6 * (u ^ 6)⁻¹)
        ≤ (11056 / 10000) * ((8 / 5) * u ^ 4)
            * ((1 / 2) * (u ^ 3)⁻¹ + 6 * (u ^ 6)⁻¹) :=
      mul_le_mul_of_nonneg_right hA hBnn
    have heq :
        (11056 / 10000) * ((8 / 5) * u ^ 4) * ((1 / 2) * (u ^ 3)⁻¹ + 6 * (u ^ 6)⁻¹)
        = (88448 / 50000) * ((1 / 2) * u + 6 * (u ^ 2)⁻¹) := by
      field_simp
      ring
    have hfin : (88448 / 50000) * ((1 / 2) * u + 6 * (u ^ 2)⁻¹) ≤ u + 1 := by
      have h2 : (23 / 5 : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by norm_num) h4u 2
      have hle : (530688 / 50000) * (u ^ 2)⁻¹ ≤ 1 := by
        rw [mul_inv_le_iff₀ (by positivity)]
        nlinarith [h2]
      have hle2 : (44224 / 50000) * u ≤ u := by nlinarith [hu0]
      have e2 : (88448 / 50000) * ((1 / 2) * u + 6 * (u ^ 2)⁻¹)
          = (44224 / 50000) * u + (530688 / 50000) * (u ^ 2)⁻¹ := by
        field_simp
        ring
      rw [e2]; linarith [hle, hle2]
    linarith [hstep, heq, hfin]
  have hcore : 13 * u + 14 ≤ (1 / 100) * u ^ 6 := by
    have h5 : (23 / 5 : ℝ) ^ 5 ≤ u ^ 5 := pow_le_pow_left₀ (by norm_num) h4u 5
    have h6 : u * (23 / 5 : ℝ) ^ 5 ≤ u ^ 6 := by nlinarith [h5, hu0]
    nlinarith [h6, h4u]
  linarith [hterm1, hterm3, hcore]

end Work.RHContract.A.RegionIII
