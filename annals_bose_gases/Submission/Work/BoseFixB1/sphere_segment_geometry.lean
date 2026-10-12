import Mathlib.Analysis.InnerProductSpace.PiL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

/-- **Geometry of the radial segment to the sphere.**  For every `x` in the closed ball of
radius `2` in `ℝ³` there is a point `y` on the sphere of radius `2` such that `‖y - x‖ = 2 - ‖x‖`
and such that every point of the segment from `x` to `y` lies in the closed ball of radius `2`
and has norm at least `‖x‖`.

Constructive witness: `y = 2 • u` where `u = ‖x‖⁻¹ • x` when `x ≠ 0` (the radial direction)
and `u` any unit vector (e.g. a standard basis vector) when `x = 0`. -/
theorem sphere_segment_geometry (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ ≤ 2) :
    ∃ y : EuclideanSpace ℝ (Fin 3), ‖y‖ = 2 ∧ ‖y - x‖ = 2 - ‖x‖ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x + t • (y - x)‖ ∧ ‖x + t • (y - x)‖ ≤ 2 := by
  -- Write `‖x‖` as an opaque real `r`, so that the substitution `x = r • u` below can never
  -- touch the occurrences of `x` sitting inside `‖x‖`.
  set r : ℝ := ‖x‖ with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact norm_nonneg x
  have hr2 : r ≤ 2 := by rw [hr]; exact hx
  -- `u` is the radial direction; then `x = r • u` and `‖u‖ = 1`.
  obtain ⟨u, hu1, hxu⟩ : ∃ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 ∧ x = r • u := by
    by_cases hx0 : x = 0
    · refine ⟨EuclideanSpace.single 0 1, ?_, ?_⟩
      · rw [EuclideanSpace.norm_single, norm_one]
      · simp only [hx0, hr, norm_zero, zero_smul]
    · have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
      refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
          inv_mul_cancel₀ hnx]
      · rw [hr, smul_smul, mul_inv_cancel₀ hnx, one_smul]
  have h2r : (0 : ℝ) ≤ 2 - r := by linarith
  have hsub : (2 : ℝ) • u - x = (2 - r) • u := by
    rw [hxu]
    exact (sub_smul 2 r u).symm
  refine ⟨(2 : ℝ) • u, ?_, ?_, ?_⟩
  · rw [norm_smul_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num), hu1, mul_one]
  · rw [hsub, norm_smul_of_nonneg h2r, hu1, mul_one]
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hkey : x + t • ((2 : ℝ) • u - x) = (r + t * (2 - r)) • u := by
      rw [hsub, hxu, smul_smul, ← add_smul]
    have hc0 : 0 ≤ r + t * (2 - r) := by
      have h := mul_nonneg ht0 h2r
      linarith
    rw [hkey, norm_smul_of_nonneg hc0, hu1, mul_one]
    constructor
    · have h := mul_nonneg ht0 h2r
      linarith
    · have h : t * (2 - r) ≤ 2 - r := by
        simpa using mul_le_mul_of_nonneg_right ht1 h2r
      linarith

end Work.BoseFixB1
