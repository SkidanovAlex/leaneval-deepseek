import Mathlib
import Submission.Work.KMTAreas.A5.interpDefs

namespace Work.KMTAreas.A5

open MeasureTheory Classical
open scoped ENNReal NNReal BigOperators

theorem pairIntegral_expansion (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ))
    (hlin₁ : ∀ (u u' v : ℤ → ℂ) (c : ℂ), Work.KMTAreas.A5.BoundedZ u → Work.KMTAreas.A5.BoundedZ u' → Work.KMTAreas.A5.BoundedZ v →
      T (u + c • u') v = T u v + c • T u' v)
    (hlin₂ : ∀ (u v v' : ℤ → ℂ) (c : ℂ), Work.KMTAreas.A5.BoundedZ u → Work.KMTAreas.A5.BoundedZ v → Work.KMTAreas.A5.BoundedZ v' →
      T u (v + c • v') = T u v + c • T u v')
    (F G : MeasureTheory.SimpleFunc ℤ ℂ) (φ : ℤ → ℂ) (hφ : ∀ x : ℤ, ‖φ x‖ ≤ 1)
    (hT : ∀ c ∈ F.range, c ≠ 0 → ∀ d ∈ G.range, d ≠ 0 →
      MeasureTheory.MemLp (T (Set.indicator (F ⁻¹' {c}) (fun _ => (1 : ℂ)))
        (Set.indicator (G ⁻¹' {d}) (fun _ => (1 : ℂ)))) 1 MeasureTheory.Measure.count)
    (a₀ a₁ b₀ b₁ z : ℂ) :
    (∫ x, T (Work.Analysis.Interpolation.analyticFamily (F : ℤ → ℂ) a₀ a₁ z)
        (Work.Analysis.Interpolation.analyticFamily (G : ℤ → ℂ) b₀ b₁ z) x * φ x
        ∂MeasureTheory.Measure.count)
      = ∑ c ∈ F.range, ∑ d ∈ G.range,
          (Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily a₀ a₁ z)
            * Work.Analysis.Interpolation.phasePow d (Work.Analysis.Interpolation.expFamily b₀ b₁ z))
          * (∫ x, T (Set.indicator (F ⁻¹' {c}) (fun _ => (1 : ℂ)))
                (Set.indicator (G ⁻¹' {d}) (fun _ => (1 : ℂ))) x * φ x
              ∂MeasureTheory.Measure.count) := by
  classical
  -- the test function is bounded, hence in `ℓ^∞`
  have hφm : MemLp φ ⊤ Measure.count := by
    refine memLp_top_of_bound (measurable_of_countable φ).aestronglyMeasurable 1 ?_
    filter_upwards with y
    exact hφ y
  -- the level-set expansion of `T` on the two analytic families
  have key := Work.KMTAreas.A5.interpExpansion T hlin₁ hlin₂ F G a₀ a₁ b₀ b₁ z
  have hpoint : ∀ y : ℤ,
      T (Work.Analysis.Interpolation.analyticFamily (F : ℤ → ℂ) a₀ a₁ z)
        (Work.Analysis.Interpolation.analyticFamily (G : ℤ → ℂ) b₀ b₁ z) y * φ y
      = ∑ c ∈ F.range, ∑ d ∈ G.range,
          (Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily a₀ a₁ z)
            * Work.Analysis.Interpolation.phasePow d (Work.Analysis.Interpolation.expFamily b₀ b₁ z))
          * ((T (Set.indicator (F ⁻¹' {c}) (fun _ => (1 : ℂ)))
                (Set.indicator (G ⁻¹' {d}) (fun _ => (1 : ℂ)))) y * φ y) := by
    intro y
    rw [key]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    ring
  -- integrability of the summands
  have hint : ∀ c ∈ F.range, ∀ d ∈ G.range,
      Integrable (fun y : ℤ =>
        (Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily a₀ a₁ z)
          * Work.Analysis.Interpolation.phasePow d (Work.Analysis.Interpolation.expFamily b₀ b₁ z))
        * ((T (Set.indicator (F ⁻¹' {c}) (fun _ => (1 : ℂ)))
              (Set.indicator (G ⁻¹' {d}) (fun _ => (1 : ℂ)))) y * φ y)) Measure.count := by
    intro c hc d hd
    by_cases hc0 : c = 0
    · subst hc0
      have hz : (fun y : ℤ =>
          (Work.Analysis.Interpolation.phasePow 0 (Work.Analysis.Interpolation.expFamily a₀ a₁ z)
            * Work.Analysis.Interpolation.phasePow d (Work.Analysis.Interpolation.expFamily b₀ b₁ z))
          * ((T (Set.indicator (F ⁻¹' {0}) (fun _ => (1 : ℂ)))
                (Set.indicator (G ⁻¹' {d}) (fun _ => (1 : ℂ)))) y * φ y)) = 0 := by
        funext y
        simp [Work.Analysis.Interpolation.phasePow_zero_left]
      rw [hz]
      exact integrable_zero ℤ ℂ Measure.count
    by_cases hd0 : d = 0
    · subst hd0
      have hz : (fun y : ℤ =>
          (Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily a₀ a₁ z)
            * Work.Analysis.Interpolation.phasePow 0 (Work.Analysis.Interpolation.expFamily b₀ b₁ z))
          * ((T (Set.indicator (F ⁻¹' {c}) (fun _ => (1 : ℂ)))
                (Set.indicator (G ⁻¹' {0}) (fun _ => (1 : ℂ)))) y * φ y)) = 0 := by
        funext y
        simp [Work.Analysis.Interpolation.phasePow_zero_left]
      rw [hz]
      exact integrable_zero ℤ ℂ Measure.count
    · exact ((hT c hc hc0 d hd hd0).integrable_mul hφm).const_mul _
  -- exchange the integral with the finite double sum
  rw [show (∫ x, T (Work.Analysis.Interpolation.analyticFamily (F : ℤ → ℂ) a₀ a₁ z)
        (Work.Analysis.Interpolation.analyticFamily (G : ℤ → ℂ) b₀ b₁ z) x * φ x
        ∂Measure.count)
      = ∫ x, (∑ c ∈ F.range, ∑ d ∈ G.range,
          (Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily a₀ a₁ z)
            * Work.Analysis.Interpolation.phasePow d (Work.Analysis.Interpolation.expFamily b₀ b₁ z))
          * ((T (Set.indicator (F ⁻¹' {c}) (fun _ => (1 : ℂ)))
                (Set.indicator (G ⁻¹' {d}) (fun _ => (1 : ℂ)))) x * φ x)) ∂Measure.count from
    integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_finsetSum _ (fun c hc => integrable_finsetSum _ (fun d hd => hint c hc d hd))]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [integral_finsetSum _ (fun d hd => hint c hc d hd)]
  exact Finset.sum_congr rfl fun d hd => integral_const_mul _ _

end Work.KMTAreas.A5
