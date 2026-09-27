import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.CircleAverage

open Complex MeasureTheory Metric Real Set Filter Topology
open scoped Real Interval

namespace Commons.Analysis.Complex.Harmonic

theorem eq_zero_on_sphere_of_circleAverage_eq_zero {f : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hfcont : ContinuousOn f (sphere c |R|))
    (hf : ∀ x ∈ sphere c |R|, 0 ≤ f x) (havg : Real.circleAverage f c R = 0) :
    ∀ x ∈ sphere c |R|, f x = 0 := by
  let g : ℝ → ℝ := fun θ => f (circleMap c R θ)
  have hmem : ∀ θ, circleMap c R θ ∈ sphere c |R| := fun θ => circleMap_mem_sphere' c R θ
  have hcont_g : Continuous g := by
    exact continuousOn_univ.mp
      (hfcont.comp (continuous_circleMap c R).continuousOn (fun θ _ => hmem θ))
  have hnonneg : ∀ θ, 0 ≤ g θ := fun θ => hf (circleMap c R θ) (hmem θ)
  have hscal : (2 * π)⁻¹ * (∫ θ in 0..2 * π, g θ) = 0 := by
    rw [Real.circleAverage_def] at havg
    simpa [g, smul_eq_mul] using havg
  have h2πne : (2 : ℝ) * π ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hint0 : (∫ θ in 0..2 * π, g θ) = 0 := by
    rcases mul_eq_zero.mp hscal with hleft | hright
    · exact False.elim ((inv_ne_zero h2πne) hleft)
    · exact hright
  have h2πpos : (0 : ℝ) < 2 * π := by positivity
  have hab : (0 : ℝ) ≤ 2 * π := le_of_lt h2πpos
  have hgII : IntervalIntegrable g volume 0 (2 * π) := hcont_g.intervalIntegrable 0 (2 * π)
  have haeIoc : g =ᵐ[volume.restrict (Ioc 0 (2 * π))] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab
        (ae_of_all (volume.restrict (Ioc 0 (2 * π))) hnonneg) hgII).mp hint0
  have haeIoo : g =ᵐ[volume.restrict (Ioo 0 (2 * π))] 0 :=
    ae_restrict_of_ae_restrict_of_subset
      (show Ioo 0 (2 * π) ⊆ Ioc 0 (2 * π) from Set.Ioo_subset_Ioc_self (a := 2 * π) (b := 0))
      haeIoc
  have hEqOnIoo : Set.EqOn g (fun _ => 0) (Ioo 0 (2 * π)) := by
    exact MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := volume) haeIoo isOpen_Ioo
      hcont_g.continuousOn continuous_const.continuousOn
  have hEqOnIcc : Set.EqOn g (fun _ => 0) (Icc 0 (2 * π)) := by
    have hcl := hEqOnIoo.closure hcont_g continuous_const
    simpa [closure_Ioo (ne_of_gt h2πpos)] using hcl
  intro x hx
  have hximg : x ∈ circleMap c R '' Ioc 0 (2 * π) := by
    simpa [image_circleMap_Ioc] using hx
  rcases hximg with ⟨θ, hθIoc, rfl⟩
  exact hEqOnIcc (Set.Ioc_subset_Icc_self (a := 0) (b := 2 * π) hθIoc)

end Commons.Analysis.Complex.Harmonic