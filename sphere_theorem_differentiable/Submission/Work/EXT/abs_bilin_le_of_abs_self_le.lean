import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.EXT

/-- A symmetric bilinear form `B` on a real inner product space that is bounded by
`K * ‖w‖ ^ 2` on the diagonal is bounded by `K * ‖u‖ * ‖v‖` in general.
Proof: polarization identity `4 * B u v = B (u+v) (u+v) - B (u-v) (u-v)`, the
parallelogram law, and normalization of `u` and `v`. -/
theorem abs_bilin_le_of_abs_self_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ u v : V, B u v = B v u)
    {K : ℝ} (hK : 0 ≤ K) (h : ∀ w : V, |B w w| ≤ K * ‖w‖ ^ 2) (u v : V) :
    |B u v| ≤ K * ‖u‖ * ‖v‖ := by
  have _hK : (0 : ℝ) ≤ K := hK
  -- Polarization identity for the symmetric bilinear form `B`.
  have pol : ∀ x y : V, 4 * B x y = B (x + y) (x + y) - B (x - y) (x - y) := by
    intro x y
    have h1 : B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
      simp only [map_add, LinearMap.add_apply]
      abel
    have h2 : B (x - y) (x - y) = B x x - B x y - B y x + B y y := by
      simp only [map_sub, LinearMap.sub_apply]
      abel
    rw [h1, h2, hB y x]
    ring
  -- General bound `|B x y| ≤ (K/2) * (‖x‖^2 + ‖y‖^2)`.
  have hgen : ∀ x y : V, |B x y| ≤ (K / 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    intro x y
    have h4 := pol x y
    have hnorm4 : |4 * B x y| = 4 * |B x y| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    have htri : |B (x + y) (x + y) - B (x - y) (x - y)| ≤
        |B (x + y) (x + y)| + |B (x - y) (x - y)| := by
      have := abs_sub_le (B (x + y) (x + y)) 0 (B (x - y) (x - y))
      simpa only [sub_zero, zero_sub, abs_neg] using this
    have hb1 := h (x + y)
    have hb2 := h (x - y)
    have hpar := parallelogram_law_with_norm ℝ x y
    calc |B x y| = (1 / 4) * |4 * B x y| := by rw [hnorm4]; ring
      _ = (1 / 4) * |B (x + y) (x + y) - B (x - y) (x - y)| := by rw [h4]
      _ ≤ (1 / 4) * (|B (x + y) (x + y)| + |B (x - y) (x - y)|) := by
          apply mul_le_mul_of_nonneg_left htri; norm_num
      _ ≤ (1 / 4) * (K * ‖x + y‖ ^ 2 + K * ‖x - y‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left (add_le_add hb1 hb2); norm_num
      _ = (K / 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
          rw [← mul_add, hpar]; ring
  by_cases hu : ‖u‖ = 0
  · have : u = 0 := norm_eq_zero.mp hu
    rw [this]; simp
  · by_cases hv : ‖v‖ = 0
    · have : v = 0 := norm_eq_zero.mp hv
      rw [this]; simp
    · have hnu : ‖(‖u‖)⁻¹ • u‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u))]
        exact inv_mul_cancel₀ hu
      have hnv : ‖(‖v‖)⁻¹ • v‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
        exact inv_mul_cancel₀ hv
      have h1 : B ((‖u‖)⁻¹ • u) ((‖v‖)⁻¹ • v) = (‖u‖)⁻¹ * ((‖v‖)⁻¹ * B u v) := by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
      have hBuv : B u v = ‖u‖ * ‖v‖ * B ((‖u‖)⁻¹ • u) ((‖v‖)⁻¹ • v) := by
        rw [h1]; field_simp
      have hbound : |B ((‖u‖)⁻¹ • u) ((‖v‖)⁻¹ • v)| ≤ K := by
        have hh := hgen ((‖u‖)⁻¹ • u) ((‖v‖)⁻¹ • v)
        rw [hnu, hnv] at hh
        linarith [hh]
      have hfinal : |B u v| = ‖u‖ * ‖v‖ * |B ((‖u‖)⁻¹ • u) ((‖v‖)⁻¹ • v)| := by
        rw [hBuv, abs_mul, abs_mul, abs_of_nonneg (norm_nonneg u),
          abs_of_nonneg (norm_nonneg v)]
      rw [hfinal]
      calc ‖u‖ * ‖v‖ * |B ((‖u‖)⁻¹ • u) ((‖v‖)⁻¹ • v)|
            ≤ ‖u‖ * ‖v‖ * K := by
              apply mul_le_mul_of_nonneg_left hbound; positivity
        _ = K * ‖u‖ * ‖v‖ := by ring

end Work.EXT
