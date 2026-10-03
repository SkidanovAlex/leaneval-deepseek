import Mathlib

namespace Work.KMTAreas

/-- The elementary duality identity underlying the Krause–Mirek–Tao `MSW` transfer:
if `0 ≤ Q`, `0 ≤ A`, `1 < q` and `Q ≤ A * Q ^ (1/(q/(q-1))) = A * Q ^ ((q-1)/q)`,
then `Q ≤ A ^ q`.

Indeed, writing `c = Q ^ (1/q)` (so that `c ^ q = Q` and `Q ^ ((q-1)/q) = c ^ (q-1)`),
the hypothesis becomes `c ^ (q-1) * c ≤ c ^ (q-1) * A`, whence `c ≤ A` (trivially when
`c = 0`) and therefore `Q = c ^ q ≤ A ^ q`. -/
theorem MSW_dual_algebra {Q A : ℝ} (hQ : 0 ≤ Q) (hA : 0 ≤ A) {q : ℝ} (hq : 1 < q)
    (h : Q ≤ A * Q ^ (1 / (q / (q - 1)))) : Q ≤ A ^ q := by
  have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hqq : 1 / (q / (q - 1)) = (q - 1) / q := by rw [one_div_div]
  rw [hqq] at h
  set c : ℝ := Q ^ (1 / q) with hcdef
  have hcnonneg : 0 ≤ c := Real.rpow_nonneg hQ _
  have hcq : c ^ q = Q := by
    rw [hcdef, ← Real.rpow_mul hQ (1 / q) q]
    have : (1 / q) * q = 1 := by rw [div_mul_cancel₀]; exact hqne
    rw [this, Real.rpow_one]
  have hcKm1 : Q ^ ((q - 1) / q) = c ^ (q - 1) := by
    rw [hcdef, ← Real.rpow_mul hQ (1 / q) (q - 1)]
    congr 1
    rw [div_mul_eq_mul_div, one_mul]
  rw [hcKm1] at h
  rw [← hcq] at h
  have hcA : c ≤ A := by
    by_cases hc0 : c = 0
    · rw [hc0]; exact hA
    · have hcpos : 0 < c := lt_of_le_of_ne hcnonneg (Ne.symm hc0)
      have hmul : c ^ (q - 1) * c ≤ c ^ (q - 1) * A := by
        calc c ^ (q - 1) * c = c ^ (q - 1) * c ^ (1:ℝ) := by rw [Real.rpow_one]
          _ = c ^ ((q - 1) + 1) := (Real.rpow_add hcpos (q - 1) 1).symm
          _ = c ^ q := by congr 1; ring
          _ ≤ A * c ^ (q - 1) := h
          _ = c ^ (q - 1) * A := by ring
      exact le_of_mul_le_mul_left hmul (Real.rpow_pos_of_pos hcpos (q - 1))
  calc Q = c ^ q := hcq.symm
    _ ≤ A ^ q := Real.rpow_le_rpow hcnonneg hcA (le_of_lt hq0)

end Work.KMTAreas
