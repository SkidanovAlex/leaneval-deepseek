import Mathlib

/-!
# A bounded function times the Fourier transform of a Schwartz function is `L¹ ∩ L²`

If `N : ℝ → ℂ` is a.e. strongly measurable and bounded by a constant `A`, and `G` is a
Schwartz function on `ℝ`, then `ξ ↦ N ξ * 𝓕 G ξ` is integrable and belongs to `L²`.

The point is that the Fourier transform of a Schwartz function is again Schwartz
(`SchwartzMap.fourier_coe`, `SchwartzMap.integrable`, `SchwartzMap.memLp`), so it is both
integrable and square integrable, and multiplying by a bounded function preserves both properties
(`Integrable.mono'`, `MemLp.of_le_mul`).
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped FourierTransform

/-- The general statement: a function bounded by `A` times a Schwartz function is in `L¹ ∩ L²`. -/
lemma integrable_memLp2_mul_schwartz (N : ℝ → ℂ) (A : ℝ)
    (hN : MeasureTheory.AEStronglyMeasurable N MeasureTheory.volume) (hNA : ∀ ξ : ℝ, ‖N ξ‖ ≤ A)
    (F : SchwartzMap ℝ ℂ) :
    MeasureTheory.Integrable (fun ξ : ℝ => N ξ * F ξ)
      ∧ MeasureTheory.MemLp (fun ξ : ℝ => N ξ * F ξ) 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have hFmeas : AEStronglyMeasurable (fun ξ : ℝ => F ξ) volume :=
    F.continuous.aestronglyMeasurable
  have hprod_meas : AEStronglyMeasurable (fun ξ : ℝ => N ξ * F ξ) volume := hN.mul hFmeas
  have hbound : ∀ ξ : ℝ, ‖N ξ * F ξ‖ ≤ A * ‖F ξ‖ := fun ξ => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hNA ξ) (norm_nonneg _)
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' ?_ hprod_meas (ae_of_all _ hbound)
    exact ((SchwartzMap.integrable F).norm).const_mul A
  · exact MemLp.of_le_mul (SchwartzMap.memLp F 2 volume) hprod_meas (ae_of_all _ hbound)

theorem integrable_memLp2_mul_fourierSchwartz (N : ℝ → ℂ) (A : ℝ)
    (hN : MeasureTheory.AEStronglyMeasurable N MeasureTheory.volume) (hNA : ∀ ξ : ℝ, ‖N ξ‖ ≤ A)
    (G : SchwartzMap ℝ ℂ) :
    MeasureTheory.Integrable (fun ξ : ℝ => N ξ * FourierTransform.fourier (G : ℝ → ℂ) ξ)
      ∧ MeasureTheory.MemLp (fun ξ : ℝ => N ξ * FourierTransform.fourier (G : ℝ → ℂ) ξ) 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have hcoe : (fun ξ : ℝ => (𝓕 G : SchwartzMap ℝ ℂ) ξ) = FourierTransform.fourier (G : ℝ → ℂ) :=
    SchwartzMap.fourier_coe G
  have hmain := integrable_memLp2_mul_schwartz N A hN hNA (𝓕 G : SchwartzMap ℝ ℂ)
  rw [← hcoe]
  exact hmain

end Work.BourgainPlan.Maximal
