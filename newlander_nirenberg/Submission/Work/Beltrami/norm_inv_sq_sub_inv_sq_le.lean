import Mathlib

namespace Work.Beltrami

/-- Elementary difference estimate for the singular kernel `w ↦ w⁻²`: if `‖v‖ ≥ ‖u‖/2`
(guaranteed by `2 * ‖u - v‖ ≤ ‖u‖`), then `‖u⁻² - v⁻²‖ ≤ 6 ‖u - v‖ / ‖u‖³`. -/
theorem norm_inv_sq_sub_inv_sq_le {u v : ℂ} (h : 2 * ‖u - v‖ ≤ ‖u‖) :
    ‖(u ^ 2)⁻¹ - (v ^ 2)⁻¹‖ ≤ 6 * ‖u - v‖ / ‖u‖ ^ 3 := by
  by_cases hu : u = 0
  · -- If `u = 0` then the hypothesis forces `v = 0` and both sides vanish.
    subst hu
    have hv : v = 0 := by
      have h' : 2 * ‖v‖ ≤ 0 := by simpa using h
      have : ‖v‖ = 0 := by linarith [norm_nonneg v]
      exact norm_eq_zero.mp this
    subst hv
    simp
  · have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    -- The hypothesis rules out `v = 0`.
    have hv : v ≠ 0 := by
      intro hv0
      rw [hv0] at h
      simp only [sub_zero] at h
      nlinarith [hu_pos]
    have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    -- `‖u‖ ≤ 2 ‖v‖`, from the triangle inequality and `2‖u - v‖ ≤ ‖u‖`.
    have hA : ‖u‖ ≤ 2 * ‖v‖ := by
      have hd : ‖u - v‖ ≤ ‖u‖ / 2 := by linarith
      have h1 : ‖u‖ ≤ ‖v‖ + ‖u - v‖ := by
        have heq : v + (u - v) = u := by ring
        calc ‖u‖ = ‖v + (u - v)‖ := by rw [heq]
          _ ≤ ‖v‖ + ‖u - v‖ := norm_add_le _ _
      linarith
    -- `‖u + v‖ ≤ 3 ‖v‖`.
    have hB : ‖u + v‖ ≤ 3 * ‖v‖ := by
      have := norm_add_le u v
      linarith
    -- The sharp product bound `‖u‖ * ‖u + v‖ ≤ 6 ‖v‖²`.
    have hC : ‖u‖ * ‖u + v‖ ≤ 6 * ‖v‖ ^ 2 := by
      have h1 : ‖u‖ * ‖u + v‖ ≤ (2 * ‖v‖) * (3 * ‖v‖) :=
        mul_le_mul hA hB (norm_nonneg _) (by positivity)
      nlinarith [h1]
    -- Exact expression of the difference of the two inverse squares.
    have hkey : ‖(u ^ 2)⁻¹ - (v ^ 2)⁻¹‖ = ‖u - v‖ * ‖u + v‖ / (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
      have h1 : (u ^ 2)⁻¹ - (v ^ 2)⁻¹ = (v - u) * (u + v) * ((u ^ 2) * (v ^ 2))⁻¹ := by
        field_simp
        ring
      rw [h1, norm_mul, norm_mul, norm_inv, norm_mul, norm_pow, norm_pow, norm_sub_rev,
        div_eq_mul_inv]
    rw [hkey, div_le_div_iff₀ (by positivity) (by positivity)]
    have hmul : ‖u - v‖ * (‖u‖ * ‖u + v‖) ≤ ‖u - v‖ * (6 * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hC (norm_nonneg _)
    nlinarith [hmul]

end Work.Beltrami
