import Mathlib

namespace Work.BourgainPlan.Maximal

/-- Dilation-constant bookkeeping for the polynomial maximal function: if `q.eval N > 0`,
`q.eval N ≤ C₀ * N ^ q.natDegree` and `q.natDegree ≥ 1`, then the constant
`C₀ ^ ((deg-1)/deg) / c` times the "dilated" weight is bounded by `2 deg C₀ N / c`.
The point is that `(q.eval N) ^ (1/deg) ≤ C₀ ^ (1/deg) * N`, so the two fractional
powers of `C₀` combine to `C₀ ^ 1 = C₀`. -/
theorem dilation_const_bound (q : Polynomial ℝ) {c C₀ N : ℝ} (hc : 0 < c) (hC₀ : 0 < C₀)
    (hd : 0 < q.natDegree) (hN : 0 < N)
    (hupper : q.eval N ≤ C₀ * N ^ q.natDegree) (hqN : 0 < q.eval N) :
    C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c
        * (2 * ((q.natDegree : ℝ) * (q.eval N) ^ ((q.natDegree : ℝ)⁻¹)))
      ≤ 2 * (q.natDegree : ℝ) * C₀ / c * N := by
  set d : ℝ := (q.natDegree : ℝ) with hd_def
  have hd_pos : 0 < d := by rw [hd_def]; exact_mod_cast hd
  have hd_ne : d ≠ 0 := ne_of_gt hd_pos
  have hN_nonneg : 0 ≤ N := le_of_lt hN
  set Q : ℝ := q.eval N with hQ_def
  have hQ_pos : 0 < Q := by rw [hQ_def]; exact hqN
  have hpow : N ^ q.natDegree = N ^ d := by
    rw [hd_def]; exact (Real.rpow_natCast N q.natDegree).symm
  have hupper' : Q ≤ C₀ * N ^ d := by
    rw [hQ_def, ← hpow]; exact hupper
  have hr : 0 ≤ d⁻¹ := inv_nonneg.mpr (le_of_lt hd_pos)
  have h1 : Q ^ d⁻¹ ≤ (C₀ * N ^ d) ^ d⁻¹ :=
    Real.rpow_le_rpow (le_of_lt hQ_pos) hupper' hr
  have h2 : (C₀ * N ^ d) ^ d⁻¹ = C₀ ^ d⁻¹ * (N ^ d) ^ d⁻¹ :=
    Real.mul_rpow (le_of_lt hC₀) (Real.rpow_nonneg hN_nonneg d)
  have h3 : (N ^ d) ^ d⁻¹ = N := by
    rw [← Real.rpow_mul hN_nonneg]
    have hmul : d * d⁻¹ = 1 := mul_inv_cancel₀ hd_ne
    rw [hmul, Real.rpow_one]
  have h4 : Q ^ d⁻¹ ≤ C₀ ^ d⁻¹ * N := by
    rw [h2, h3] at h1; exact h1
  have key : C₀ ^ ((d - 1) / d) * Q ^ d⁻¹ ≤ C₀ * N := by
    have h5 := mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg (le_of_lt hC₀) ((d-1)/d))
    have h6 : C₀ ^ ((d - 1) / d) * (C₀ ^ d⁻¹ * N) = C₀ * N := by
      rw [← mul_assoc, ← Real.rpow_add hC₀ ((d-1)/d) d⁻¹]
      have hexp : (d - 1) / d + d⁻¹ = 1 := by
        rw [inv_eq_one_div, ← add_div, sub_add_cancel, div_self hd_ne]
      rw [hexp, Real.rpow_one]
    linarith [h5, h6]
  have h2dc : 0 < 2 * d / c := div_pos (by linarith) hc
  calc (C₀ ^ ((d - 1) / d) / c) * (2 * (d * Q ^ d⁻¹))
      = (2 * d / c) * (C₀ ^ ((d - 1) / d) * Q ^ d⁻¹) := by ring
    _ ≤ (2 * d / c) * (C₀ * N) := mul_le_mul_of_nonneg_left key (le_of_lt h2dc)
    _ = 2 * d * C₀ / c * N := by ring

end Work.BourgainPlan.Maximal
