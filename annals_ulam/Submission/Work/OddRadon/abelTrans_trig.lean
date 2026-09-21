import Mathlib
import Submission.Work.OddRadon.Abel

namespace Work.OddRadon

open MeasureTheory
open scoped Interval

/-- **The trigonometric (polar) form of the forward Abel-type transform.**

Substituting `s = c sin θ` in `T_α G c = ∫_0^c G s (c² - s²)^α ds` gives
`T_α G c = c^(2α+1) ∫_0^{π/2} G (c sin θ) (cos θ)^(2α+1) dθ`.

The substitution `θ ↦ c sin θ` is a `C¹` monotone map on `[0, π/2]` with derivative `c cos θ ≥ 0`,
so `intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg` applies with no regularity
hypothesis on `G`. The pointwise simplification of the integrand is valid off `θ = π/2`, and the
two integrands therefore agree almost everywhere (they may differ at the single point `π/2`). -/
theorem abelTrans_trig {α : ℝ} (G : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    abelTrans α G c = c ^ (2 * α + 1) *
      ∫ θ in (0 : ℝ)..(Real.pi / 2),
        G (c * Real.sin θ) * Real.cos θ ^ (2 * α + 1) := by
  rw [abelTrans]
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hmin : min (0 : ℝ) (Real.pi / 2) = 0 := min_eq_left hpi2.le
  have hmax : max (0 : ℝ) (Real.pi / 2) = Real.pi / 2 := max_eq_right hpi2.le
  have hcont : ContinuousOn (fun θ : ℝ => c * Real.sin θ) (Set.uIcc (0 : ℝ) (Real.pi / 2)) :=
    (continuous_const.mul Real.continuous_sin).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (min (0 : ℝ) (Real.pi / 2)) (max (0 : ℝ) (Real.pi / 2)),
      HasDerivAt (fun θ : ℝ => c * Real.sin θ) (c * Real.cos x) x := by
    intro x _
    exact (Real.hasDerivAt_sin x).const_mul c
  have hnonneg : ∀ x ∈ Set.Ioo (min (0 : ℝ) (Real.pi / 2)) (max (0 : ℝ) (Real.pi / 2)),
      0 ≤ c * Real.cos x := by
    intro x hx
    rw [hmin, hmax] at hx
    refine mul_nonneg hc.le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
    · linarith [Real.pi_pos, hx.1]
    · linarith [Real.pi_pos, hx.2]
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun θ : ℝ => c * Real.sin θ) (f' := fun θ : ℝ => c * Real.cos θ)
    (g := fun s : ℝ => G s * (c ^ 2 - s ^ 2) ^ α) (a := (0 : ℝ)) (b := Real.pi / 2)
    hcont hderiv hnonneg
  simp only [Function.comp_apply, Real.sin_zero, mul_zero, Real.sin_pi_div_two, mul_one] at hsub
  rw [← hsub]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  have hcompl : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({0, Real.pi / 2} : Set ℝ) := by
    have hfin : ({0, Real.pi / 2} : Set ℝ).Finite := (Set.finite_singleton _).insert 0
    exact MeasureTheory.compl_mem_ae_iff.mpr (hfin.measure_zero volume)
  filter_upwards [hcompl] with θ hθ hθm
  rw [Set.uIoc_of_le hpi2.le] at hθm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hθ
  have hθ0 : (0 : ℝ) < θ := hθm.1
  have hθlt : θ < Real.pi / 2 := lt_of_le_of_ne hθm.2 hθ.2
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0],
      by linarith [Real.pi_pos, hθlt]⟩
  have hx1 : c ^ 2 - (c * Real.sin θ) ^ 2 = (c * Real.cos θ) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ
    nlinarith
  have hx2 : ((c * Real.cos θ) ^ 2) ^ α = (c * Real.cos θ) ^ (2 * α) := by
    rw [← Real.rpow_two (c * Real.cos θ)]
    exact (Real.rpow_mul (mul_pos hc hcos).le 2 α).symm
  have hx3 : (c * Real.cos θ) ^ (2 * α) * (c * Real.cos θ) =
      (c * Real.cos θ) ^ (2 * α + 1) := by
    calc (c * Real.cos θ) ^ (2 * α) * (c * Real.cos θ)
        = (c * Real.cos θ) ^ (2 * α) * (c * Real.cos θ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (c * Real.cos θ) ^ (2 * α + 1) :=
            (Real.rpow_add (mul_pos hc hcos) (2 * α) 1).symm
  have hx4 : (c * Real.cos θ) ^ (2 * α + 1) = c ^ (2 * α + 1) * Real.cos θ ^ (2 * α + 1) :=
    Real.mul_rpow hc.le hcos.le
  calc G (c * Real.sin θ) * (c ^ 2 - (c * Real.sin θ) ^ 2) ^ α * (c * Real.cos θ)
      = G (c * Real.sin θ) * (c * Real.cos θ) ^ (2 * α) * (c * Real.cos θ) := by
        rw [hx1, hx2]
    _ = G (c * Real.sin θ) * ((c * Real.cos θ) ^ (2 * α) * (c * Real.cos θ)) := by ring
    _ = G (c * Real.sin θ) * (c * Real.cos θ) ^ (2 * α + 1) := by rw [hx3]
    _ = G (c * Real.sin θ) * (c ^ (2 * α + 1) * Real.cos θ ^ (2 * α + 1)) := by rw [hx4]
    _ = c ^ (2 * α + 1) * (G (c * Real.sin θ) * Real.cos θ ^ (2 * α + 1)) := by ring

end Work.OddRadon
