import Mathlib

namespace Work.OddCurve.LowSlope

open MeasureTheory
open scoped Interval

/-- **Trigonometric substitution in the Abel-type integral**, with no regularity
hypothesis on `Φ`.

For `0 < u`, the change of variables `c = u sin θ` turns
`∫_0^u c Φ c / √(u² - c²) dc` into `∫_0^{π/2} u sin θ Φ (u sin θ) dθ`.

The substitution is performed by
`intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg` with the monotone map
`θ ↦ u sin θ`; that lemma carries **no** regularity hypothesis on the integrand,
so no continuity or boundedness of `Φ` is needed.  The two integrands differ only
at the single point `θ = π/2` (where `cos θ = 0`), which
`intervalIntegral.integral_congr_ae` absorbs. -/
theorem abel_integral_trig_substitution_no_hyp {Φ : ℝ → ℝ} {u : ℝ} (hu : 0 < u) :
    (∫ c in (0 : ℝ)..u, c * Φ c / Real.sqrt (u ^ 2 - c ^ 2))
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), u * Real.sin θ * Φ (u * Real.sin θ) := by
  have hpi2 : (0:ℝ) < Real.pi / 2 := by positivity
  have hmin : min (0:ℝ) (Real.pi / 2) = 0 := min_eq_left hpi2.le
  have hmax : max (0:ℝ) (Real.pi / 2) = Real.pi / 2 := max_eq_right hpi2.le
  -- the substitution map `θ ↦ u sin θ` is continuous on `[0, π/2]`
  have hc : ContinuousOn (fun θ : ℝ => u * Real.sin θ) (Set.uIcc (0:ℝ) (Real.pi / 2)) :=
    (continuous_const.mul Real.continuous_sin).continuousOn
  have hd : ∀ x ∈ Set.Ioo (min (0:ℝ) (Real.pi / 2)) (max (0:ℝ) (Real.pi / 2)),
      HasDerivAt (fun θ : ℝ => u * Real.sin θ) (u * Real.cos x) x := by
    intro x _
    exact (Real.hasDerivAt_sin x).const_mul u
  have hn : ∀ x ∈ Set.Ioo (min (0:ℝ) (Real.pi / 2)) (max (0:ℝ) (Real.pi / 2)),
      0 ≤ u * Real.cos x := by
    intro x hx
    rw [hmin, hmax] at hx
    exact mul_nonneg hu.le
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hx.1],
        by linarith [Real.pi_pos, hx.2]⟩)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun θ : ℝ => u * Real.sin θ) (f' := fun θ : ℝ => u * Real.cos θ)
    (g := fun c : ℝ => c * Φ c / Real.sqrt (u ^ 2 - c ^ 2)) (a := (0:ℝ)) (b := Real.pi / 2)
    hc hd hn
  simp only [Function.comp_apply, Real.sin_zero, mul_zero, Real.sin_pi_div_two, mul_one] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr_ae
  -- the two integrands agree except possibly at the single point `π/2`
  have hcompl : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({Real.pi / 2} : Set ℝ) := by
    have hfin : ({Real.pi / 2} : Set ℝ).Finite := Set.finite_singleton _
    exact MeasureTheory.compl_mem_ae_iff.mpr (hfin.measure_zero volume)
  filter_upwards [hcompl] with θ hθ hθm
  rw [Set.uIoc_of_le hpi2.le] at hθm
  simp only [Set.mem_singleton_iff] at hθ
  have hθ0 : 0 < θ := hθm.1
  have hθlt : θ < Real.pi / 2 := lt_of_le_of_ne hθm.2 hθ
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0], by linarith [Real.pi_pos, hθlt]⟩
  have hsq : u ^ 2 - (u * Real.sin θ) ^ 2 = (u * Real.cos θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsqrt : Real.sqrt (u ^ 2 - (u * Real.sin θ) ^ 2) = u * Real.cos θ := by
    rw [hsq, Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  have hne : u * Real.cos θ ≠ 0 := by positivity
  field_simp

end Work.OddCurve.LowSlope
