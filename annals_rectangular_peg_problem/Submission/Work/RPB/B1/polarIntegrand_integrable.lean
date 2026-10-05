import Mathlib
import Submission.Work.RPB.B1.PolarDefs

/-!
# Integrability of the polar integrand `polarTarget.indicator (polarIntegrand a C R)`

The polar integrand

`p ↦ if p.1 < radial a R p.2 then (C e^{-i p.2}).im else 0`

is bounded by `‖C‖` everywhere, and — once intersected with the polar target
`(0, ∞) × (-π, π)` — is supported inside the finite-measure box
`(0, ‖a‖ + R) × (-π, π)`, because `radial a R φ ≤ ‖a‖ + R`.  Hence it is integrable
for the product of the Lebesgue measures on `ℝ`.
-/

namespace Work.RPB.B1

open MeasureTheory Set Complex Real
open scoped Real

noncomputable section

/-- The radial extent `radial a R` depends continuously on the angular variable. -/
theorem continuous_radial_polar (a : ℂ) (R : ℝ) : Continuous (fun φ : ℝ => radial a R φ) := by
  unfold radial
  fun_prop

/-- Upper bound on the radial extent: `radial a R φ ≤ ‖a‖ + R` for `0 ≤ R`. -/
theorem radial_le_norm_add (a : ℂ) {R : ℝ} (hR : 0 ≤ R) (φ : ℝ) :
    radial a R φ ≤ ‖a‖ + R := by
  unfold radial
  have hnorm : ‖a * Complex.exp (-(φ : ℂ) * Complex.I)‖ = ‖a‖ := by
    rw [norm_mul, Complex.norm_exp]; simp
  have hre : (a * Complex.exp (-(φ : ℂ) * Complex.I)).re ≤ ‖a‖ := by
    rw [← hnorm]; exact Complex.re_le_norm _
  have hle : R ^ 2 - (a * Complex.exp (-(φ : ℂ) * Complex.I)).im ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_nonneg (a * Complex.exp (-(φ : ℂ) * Complex.I)).im]
  have hs : Real.sqrt (R ^ 2 - (a * Complex.exp (-(φ : ℂ) * Complex.I)).im ^ 2) ≤ R :=
    (Real.sqrt_le_left hR).2 hle
  linarith

/-- The polar integrand is measurable. -/
theorem measurable_polarIntegrand (a C : ℂ) (R : ℝ) : Measurable (polarIntegrand a C R) := by
  unfold polarIntegrand
  refine Measurable.ite ?_ ?_ ?_
  · exact (isOpen_lt continuous_fst ((continuous_radial_polar a R).comp continuous_snd)).measurableSet
  · exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      (C * Complex.exp (-(p.2 : ℂ) * Complex.I)).im)).measurable
  · exact measurable_const

/-- The polar integrand is everywhere bounded by `‖C‖`, since `‖e^{-iφ}‖ = 1`. -/
theorem norm_polarIntegrand_le (a C : ℂ) (R : ℝ) (p : ℝ × ℝ) :
    ‖polarIntegrand a C R p‖ ≤ ‖C‖ := by
  unfold polarIntegrand
  by_cases h : p.1 < radial a R p.2
  · simp only [h, ite_true, Real.norm_eq_abs]
    have h1 : ‖Complex.exp (-(p.2 : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    calc |(C * Complex.exp (-(p.2 : ℂ) * Complex.I)).im|
        ≤ ‖C * Complex.exp (-(p.2 : ℂ) * Complex.I)‖ := Complex.abs_im_le_norm _
      _ = ‖C‖ := by rw [norm_mul, h1, mul_one]
  · simp [h]

theorem polarIntegrand_integrable (a C : ℂ) {R : ℝ} (hR : ‖a‖ < R) : MeasureTheory.Integrable (polarTarget.indicator (polarIntegrand a C R)) ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  classical
  -- Reduce to integrability of the integrand *on* the polar target.
  refine (integrable_indicator_iff measurableSet_polarTarget).mpr ?_
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg a) hR
  set M : ℝ := ‖a‖ + R with hM
  have hfin : ((volume : Measure ℝ).prod (volume : Measure ℝ))
      (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi) ≠ ⊤ := by
    rw [Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  -- On the finite-measure box `(0, M) × (-π, π)` the constant `‖C‖` is integrable, and the
  -- integrand is dominated by it (pointwise, so a fortiori almost everywhere).
  have hbox : IntegrableOn (polarIntegrand a C R)
      (polarTarget ∩ (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have hc : IntegrableOn (fun _ : ℝ × ℝ => ‖C‖)
        (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi)
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
      integrableOn_const hfin
    have hc' : IntegrableOn (fun _ : ℝ × ℝ => ‖C‖)
        (polarTarget ∩ (Set.Ioo (0:ℝ) M ×ˢ Set.Ioo (-Real.pi) Real.pi))
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
      hc.mono_set Set.inter_subset_right
    exact hc'.mono' (measurable_polarIntegrand a C R).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_polarIntegrand_le a C R))
  -- The support of the integrand meets `polarTarget` only inside the box.
  refine IntegrableOn.of_inter_support measurableSet_polarTarget ?_
  refine hbox.mono_set ?_
  rintro p ⟨hpT, hpsup⟩
  obtain ⟨hp1, hp2⟩ := (show p ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi from hpT)
  have hlt : p.1 < radial a R p.2 := by
    by_contra hcon
    exact hpsup (by simp [polarIntegrand, hcon])
  refine ⟨hpT, ?_⟩
  show p.1 ∈ Set.Ioo (0:ℝ) M ∧ p.2 ∈ Set.Ioo (-Real.pi) Real.pi
  exact ⟨⟨hp1, lt_of_lt_of_le hlt (by rw [hM]; exact radial_le_norm_add a hRpos.le p.2)⟩, hp2⟩

end

end Work.RPB.B1
