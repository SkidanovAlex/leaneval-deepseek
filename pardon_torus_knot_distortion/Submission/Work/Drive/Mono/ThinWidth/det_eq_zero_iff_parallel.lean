import Mathlib

namespace Work.Drive.Mono.ThinWidth

/-- For linear functionals on the plane, the vanishing of the determinant `L(1,0)·M(0,1) −
L(0,1)·M(1,0)` is exactly the linear dependence of `L` and `M`, as long as `M ≠ 0`. -/
theorem det_eq_zero_iff_parallel {L M : (ℝ × ℝ) →L[ℝ] ℝ} (hM : M ≠ 0) :
    (L (1, 0) * M (0, 1) - L (0, 1) * M (1, 0) = 0 ↔ ∃ t : ℝ, L = t • M) := by
  -- Both functionals are determined by their values on the standard basis.
  have hL : ∀ x y : ℝ, L (x, y) = x * L (1, 0) + y * L (0, 1) := by
    intro x y
    have h : (x, y) = x • (1, 0) + y • (0, 1) := by ext <;> simp
    rw [h, map_add, map_smul, map_smul]
    simp
  have hMv : ∀ x y : ℝ, M (x, y) = x * M (1, 0) + y * M (0, 1) := by
    intro x y
    have h : (x, y) = x • (1, 0) + y • (0, 1) := by ext <;> simp
    rw [h, map_add, map_smul, map_smul]
    simp
  constructor
  · intro h
    -- `M ≠ 0` forces one of its two basis values to be nonzero.
    have hc_or_d : M (1, 0) ≠ 0 ∨ M (0, 1) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hc, hd⟩ := hcon
      exact hM (by
        apply ContinuousLinearMap.ext
        intro v
        obtain ⟨x, y⟩ := v
        simp [hMv x y, hc, hd])
    rcases hc_or_d with hc | hd
    · refine ⟨L (1, 0) / M (1, 0), ?_⟩
      apply ContinuousLinearMap.ext
      intro v
      obtain ⟨x, y⟩ := v
      rw [hL x y, smul_apply, smul_eq_mul, hMv x y]
      have h2 : L (0, 1) = (L (1, 0) / M (1, 0)) * M (0, 1) := by
        rw [div_mul_eq_mul_div, eq_div_iff hc]
        linarith [h]
      rw [h2]
      field_simp
    · refine ⟨L (0, 1) / M (0, 1), ?_⟩
      apply ContinuousLinearMap.ext
      intro v
      obtain ⟨x, y⟩ := v
      rw [hL x y, smul_apply, smul_eq_mul, hMv x y]
      have h1 : L (1, 0) = (L (0, 1) / M (0, 1)) * M (1, 0) := by
        rw [div_mul_eq_mul_div, eq_div_iff hd]
        linarith [h]
      rw [h1]
      field_simp
  · rintro ⟨t, rfl⟩
    simp only [smul_apply, smul_eq_mul]
    ring

end Work.Drive.Mono.ThinWidth
