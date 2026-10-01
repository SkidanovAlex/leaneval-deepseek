import Mathlib

namespace Work.ZeroDensity.Jutila

/-- The fundamental bound `∑_{q=1}^{M} q^{-2} ≤ 2` for every natural `M`,
obtained from Mathlib's `sum_Ioo_inv_sq_le` (the telescoping estimate
`∑_{i>k} i^{-2} ≤ 2/(k+1)`) with `k = 0`. -/
theorem sum_sq_inv_le_two (M : ℕ) :
    ∑ q ∈ Finset.Icc 1 M, ((q : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have h := sum_Ioo_inv_sq_le (k := 0) (n := M + 1) (α := ℝ)
  rw [show Finset.Ioo 0 (M + 1) = Finset.Icc 1 M from by
    ext x; simp [Finset.mem_Ioo, Finset.mem_Icc]; omega] at h
  simpa using h

theorem sum_div_sq_le (z N : ℕ) (hz : 1 ≤ z) (hN : N < z * z) :
    ∑ q ∈ Finset.Icc 1 (N / z), ((N : ℝ) / ((q : ℝ) * (z : ℝ))) ^ 2 ≤ 2 * (N : ℝ) := by
  -- factor out the constant `(N/z)^2`
  have hfactor : ∑ q ∈ Finset.Icc 1 (N / z), ((N : ℝ) / ((q : ℝ) * (z : ℝ))) ^ 2
      = ((N : ℝ) / (z : ℝ)) ^ 2 * ∑ q ∈ Finset.Icc 1 (N / z), ((q : ℝ) ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_Icc] at hq
    have hq0 : (q : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.1
      linarith
    have hz0 : (z : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
      linarith
    field_simp
  -- bound on the reciprocal-square sum
  have hsq : ∑ q ∈ Finset.Icc 1 (N / z), ((q : ℝ) ^ 2)⁻¹ ≤ 2 :=
    sum_sq_inv_le_two (N / z)
  -- `(N/z)^2 ≤ N` since `N < z^2`
  have hsqle : ((N : ℝ) / (z : ℝ)) ^ 2 ≤ (N : ℝ) := by
    have hNz : (N : ℝ) ≤ (z : ℝ) ^ 2 := by
      have h : (N : ℝ) < (z * z : ℕ) := by exact_mod_cast hN
      push_cast at h
      nlinarith
    rw [div_pow]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (z : ℝ) ^ 2)]
    nlinarith [show (0 : ℝ) ≤ (N : ℝ) by positivity]
  calc ∑ q ∈ Finset.Icc 1 (N / z), ((N : ℝ) / ((q : ℝ) * (z : ℝ))) ^ 2
      = ((N : ℝ) / (z : ℝ)) ^ 2 * ∑ q ∈ Finset.Icc 1 (N / z), ((q : ℝ) ^ 2)⁻¹ := hfactor
    _ ≤ ((N : ℝ) / (z : ℝ)) ^ 2 * 2 := by
        apply mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2 * ((N : ℝ) / (z : ℝ)) ^ 2 := by ring
    _ ≤ 2 * (N : ℝ) := by
        apply mul_le_mul_of_nonneg_left hsqle (by norm_num)

end Work.ZeroDensity.Jutila
