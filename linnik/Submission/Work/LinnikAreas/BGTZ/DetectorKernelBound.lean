import Mathlib

namespace Work.LinnikAreas.BGTZ

/-- Pointwise bound for the BGTZ vertical-line kernel: for `c > 0` and `N ≥ 1` the modulus of
`t ↦ N^{c+it}/((c+it)(c+1+it))` decays like `N^c/(1+t^2)`. -/
lemma DetectorKernelBound {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 0 < N) (t : ℝ) :
    ‖(N : ℂ) ^ (c + t * Complex.I) / ((c + t * Complex.I) * (c + 1 + t * Complex.I))‖
      ≤ (N : ℝ) ^ c * (1 + 1 / c ^ 2) * (1 + t ^ 2)⁻¹ := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNc : (0 : ℝ) < (N : ℝ) ^ c := Real.rpow_pos_of_pos hNpos c
  have hden_pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hc2pos : (0 : ℝ) < c ^ 2 := by positivity
  -- norm of the numerator: `‖N^{c+it}‖ = N^c`
  have hnum : ‖(N : ℂ) ^ (c + t * Complex.I)‖ = (N : ℝ) ^ c := by
    rw [← Complex.ofReal_natCast N,
      Complex.norm_cpow_eq_rpow_re_of_pos hNpos (c + t * Complex.I)]
    simp
  -- squared norms of the two linear factors
  have hA2 : ‖(c : ℂ) + t * Complex.I‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hB2 : ‖(c : ℂ) + 1 + t * Complex.I‖ ^ 2 = (c + 1) ^ 2 + t ^ 2 := by
    rw [show ((c : ℂ) + 1 : ℂ) = ((c + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.sq_norm, Complex.normSq_add_mul_I]
  -- positivity of the two norms
  have hAp : (0 : ℝ) < ‖(c : ℂ) + t * Complex.I‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) (Ne.symm ?_)
    intro h0
    rw [h0] at hA2
    norm_num at hA2
    have : (0 : ℝ) < c ^ 2 + t ^ 2 := by positivity
    linarith
  have hBp : (0 : ℝ) < ‖(c : ℂ) + 1 + t * Complex.I‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) (Ne.symm ?_)
    intro h0
    rw [h0] at hB2
    norm_num at hB2
    have : (0 : ℝ) < (c + 1) ^ 2 + t ^ 2 := by positivity
    linarith
  have hPpos : (0 : ℝ) < ‖(c : ℂ) + t * Complex.I‖ * ‖(c : ℂ) + 1 + t * Complex.I‖ :=
    mul_pos hAp hBp
  -- key real inequality `1 + t^2 ≤ (1 + 1/c^2) * ‖A‖ * ‖B‖`
  have hkey : 1 + t ^ 2
      ≤ (1 + 1 / c ^ 2) * (‖(c : ℂ) + t * Complex.I‖ * ‖(c : ℂ) + 1 + t * Complex.I‖) := by
    set P := ‖(c : ℂ) + t * Complex.I‖ * ‖(c : ℂ) + 1 + t * Complex.I‖ with hP
    have hPnn : (0 : ℝ) ≤ P := by positivity
    have hbase : (0 : ℝ) ≤ c ^ 2 + c + t ^ 2 := by
      nlinarith [sq_nonneg c, sq_nonneg t]
    have hP2 : P ^ 2 = (c ^ 2 + c + t ^ 2) ^ 2 + t ^ 2 := by
      rw [hP, mul_pow, hA2, hB2]
      ring
    have hsq : (c ^ 2 + c + t ^ 2) ^ 2 ≤ P ^ 2 := by
      rw [hP2]; nlinarith [sq_nonneg t]
    have hPge : c ^ 2 + c + t ^ 2 ≤ P :=
      (mul_self_le_mul_self_iff hbase hPnn).mpr (by simpa [pow_two] using hsq)
    have hpoly : (1 + t ^ 2) * c ^ 2 ≤ (c ^ 2 + 1) * (c ^ 2 + c + t ^ 2) := by
      nlinarith [hc, sq_nonneg c, sq_nonneg t]
    have h1 : (1 : ℝ) + 1 / c ^ 2 = (c ^ 2 + 1) / c ^ 2 := by field_simp
    rw [h1, div_mul_eq_mul_div, le_div_iff₀ hc2pos]
    have h2 : (c ^ 2 + 1) * (c ^ 2 + c + t ^ 2) ≤ (c ^ 2 + 1) * P :=
      mul_le_mul_of_nonneg_left hPge (by positivity)
    linarith
  -- assembly
  calc ‖(N : ℂ) ^ (c + t * Complex.I) / ((c + t * Complex.I) * (c + 1 + t * Complex.I))‖
      = (N : ℝ) ^ c / (‖(c : ℂ) + t * Complex.I‖ * ‖(c : ℂ) + 1 + t * Complex.I‖) := by
        rw [norm_div, hnum, norm_mul]
    _ ≤ (N : ℝ) ^ c * (1 + 1 / c ^ 2) / (1 + t ^ 2) := by
        rw [div_le_div_iff₀ hPpos hden_pos, mul_assoc]
        exact mul_le_mul_of_nonneg_left hkey (le_of_lt hNc)
    _ = (N : ℝ) ^ c * (1 + 1 / c ^ 2) * (1 + t ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]

end Work.LinnikAreas.BGTZ
