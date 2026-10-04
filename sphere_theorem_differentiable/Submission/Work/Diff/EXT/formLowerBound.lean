import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- A continuous bilinear form on a finite-dimensional real normed space whose associated
quadratic form is strictly positive away from the origin is bounded below by `c * ‖v‖ ^ 2`
for some `c > 0`.  (No symmetry of `B` is needed; only the diagonal `v ↦ B v v` is used.) -/
lemma exists_pos_le_bilinForm_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ c > 0, ∀ v : E, c * ‖v‖ ^ 2 ≤ B v v := by
  -- `v ↦ B v v` is continuous, so on the compact unit sphere it attains a positive minimum
  -- (and the sphere is empty exactly when `E` is a subsingleton, where any `c > 0` works).
  have hcont : Continuous fun v : E => B v v := by fun_prop
  have hmin : ∃ c > 0, ∀ v : E, ‖v‖ = 1 → c ≤ B v v := by
    rcases subsingleton_or_nontrivial E with hsub | hnt
    · refine ⟨1, one_pos, fun v hv => ?_⟩
      have hv0 : v = 0 := Subsingleton.elim v 0
      rw [hv0] at hv
      simp at hv
    · have hnt' : Nontrivial E := hnt
      have hne : (Metric.sphere (0 : E) (1 : ℝ)).Nonempty := by
        obtain ⟨v, hv⟩ := exists_ne (0 : E)
        refine ⟨‖v‖⁻¹ • v, ?_⟩
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
      obtain ⟨v, hv, hminv⟩ :=
        (isCompact_sphere (0 : E) (1 : ℝ)).exists_isMinOn hne hcont.continuousOn
      have hvnorm : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hv
      exact ⟨B v v, hB v (by intro h; rw [h] at hvnorm; norm_num at hvnorm),
        fun w hw => hminv (by simpa [Metric.mem_sphere, dist_eq_norm] using hw)⟩
  obtain ⟨c, hcpos, hc⟩ := hmin
  refine ⟨c, hcpos, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    -- scale `v` to the unit sphere
    have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ hnorm]
    have h1 : c ≤ (‖v‖⁻¹) ^ 2 * B v v := by
      have h2 := hc _ hu
      have h3 : B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v) = (‖v‖⁻¹) ^ 2 * B v v := by
        simp only [ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul]
        ring
      rwa [h3] at h2
    have hsq : (‖v‖⁻¹) ^ 2 * ‖v‖ ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hnorm, one_pow]
    have hpos : 0 < ‖v‖ ^ 2 := by positivity
    calc c * ‖v‖ ^ 2 ≤ ((‖v‖⁻¹) ^ 2 * B v v) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
      _ = B v v * ((‖v‖⁻¹) ^ 2 * ‖v‖ ^ 2) := by ring
      _ = B v v := by rw [hsq, mul_one]

/-- The sublevel set `{v | B v v < r}` of a continuous bilinear form that dominates
`c * ‖v‖ ^ 2` (`c > 0`) is von Neumann bounded. -/
lemma isVonNBounded_lt_bilinForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {B : E →L[ℝ] E →L[ℝ] ℝ} {c : ℝ} (hcpos : 0 < c)
    (hc : ∀ v : E, c * ‖v‖ ^ 2 ≤ B v v) :
    ∀ r : ℝ, 0 < r → Bornology.IsVonNBounded ℝ {v : E | B v v < r} := by
  intro r hr
  refine Bornology.IsVonNBounded.subset ?_ (NormedSpace.isVonNBounded_ball ℝ E (Real.sqrt (r / c)))
  intro v hv
  have hcr : c * ‖v‖ ^ 2 < r := lt_of_le_of_lt (hc v) hv
  have hd : ‖v‖ ^ 2 < r / c := by rw [lt_div_iff₀ hcpos]; linarith
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
    _ < Real.sqrt (r / c) := Real.sqrt_lt_sqrt (by positivity) hd

theorem formLowerBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    (∃ c > 0, ∀ v : E, c * ‖v‖ ^ 2 ≤ B v v) ∧
      (∀ r : ℝ, 0 < r → Bornology.IsVonNBounded ℝ {v : E | B v v < r}) := by
  obtain ⟨c, hcpos, hc⟩ := exists_pos_le_bilinForm_sq hB
  exact ⟨⟨c, hcpos, hc⟩, isVonNBounded_lt_bilinForm hcpos hc⟩

end Work.Diff.EXT
