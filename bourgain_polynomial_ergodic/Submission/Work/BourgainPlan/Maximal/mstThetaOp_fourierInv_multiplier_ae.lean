import Mathlib
import Submission.Work.BourgainPlan.Maximal.DRDFDefs
import Submission.Work.BourgainPlan.Maximal.BLReproGoodCase

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped FourierTransform BigOperators ENNReal

/-- The `L²` multiplier with symbol `m` applied to the inverse Fourier transform of `W` is, almost
everywhere, the inverse Fourier integral of the pointwise product `m * W`.

Indeed `multiplier m hm (𝓕⁻ (toLp W)) = 𝓕⁻ (mulLp m hm (toLp W))`, and `mulLp m hm (toLp W)` is
the `L²` class of the pointwise product `m * W` (the proof of the `MemLp` predicate being
irrelevant).  Since `m` is bounded and `W ∈ L¹ ∩ L²`, the product `m * W` is again in `L¹ ∩ L²`,
so the existing identification `fourierInv_toLp_ae_eq_fourierInv` of the `L²` inverse transform
with the inverse Fourier integral applies. -/
theorem multiplier_fourierInv_toLp_ae (m : ℝ → ℂ) (hm : MemLp m ⊤ (volume : Measure ℝ))
    (W : ℝ → ℂ) (hW1 : MemLp W 1 (volume : Measure ℝ)) (hW2 : MemLp W 2 (volume : Measure ℝ)) :
    ((Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm (𝓕⁻ (MemLp.toLp W hW2)) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] FourierTransform.fourierInv (m * W) := by
  have hZ1 : MemLp (m * W) 1 (volume : Measure ℝ) := by
    exact hm.mul hW1
  have hZ2 : MemLp (m * W) 2 (volume : Measure ℝ) := by
    exact hm.mul hW2
  have hstep : Commons.Analysis.Fourier.BoundaryLayer.mulLp m hm (MemLp.toLp W hW2)
      = MemLp.toLp (m * W) hZ2 := by
    refine Lp.ext ?_
    filter_upwards [Commons.Analysis.Fourier.BoundaryLayer.mulLp_coe m hm (MemLp.toLp W hW2),
      MemLp.coeFn_toLp hW2, MemLp.coeFn_toLp hZ2] with ξ h1 h2 h3
    simp only [Pi.mul_apply] at h1 h3 ⊢
    rw [h1, h2, h3]
  rw [show Commons.Analysis.Fourier.BoundaryLayer.multiplier m hm (𝓕⁻ (MemLp.toLp W hW2))
      = 𝓕⁻ (MemLp.toLp (m * W) hZ2) from by
    rw [Commons.Analysis.Fourier.BoundaryLayer.multiplier,
      FourierInvPair.fourier_fourierInv_eq, hstep]]
  exact Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv hZ1 hZ2

theorem mstThetaOp_fourierInv_multiplier_ae (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ)
    (hm : MeasureTheory.MemLp (fun ξ : ℝ => ∑ j ∈ Finset.range M, ε j *
        (starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P (2 ^ (j * 2 ^ i)) ξ)
         - starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P (2 ^ ((j + 1) * 2 ^ i)) ξ))) ⊤
        (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    {W : ℝ → ℂ} (hW1 : MeasureTheory.MemLp W 1 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hW2 : MeasureTheory.MemLp W 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hW : ∀ x : ℝ, FourierTransform.fourierInv (fun ξ : ℝ => (∑ j ∈ Finset.range M, ε j *
        (starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P (2 ^ (j * 2 ^ i)) ξ)
         - starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P (2 ^ ((j + 1) * 2 ^ i)) ξ))) * W ξ) x
      = Work.BourgainPlan.Maximal.mstThetaOp P i M ε (fun y : ℝ => FourierTransform.fourierInv W y) x) :
    Work.BourgainPlan.Maximal.mstThetaOp P i M ε (fun y : ℝ => FourierTransform.fourierInv W y)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)]
      ((Commons.Analysis.Fourier.BoundaryLayer.multiplier (fun ξ : ℝ => ∑ j ∈ Finset.range M, ε j *
        (starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P (2 ^ (j * 2 ^ i)) ξ)
         - starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P (2 ^ ((j + 1) * 2 ^ i)) ξ))) hm
        (FourierTransform.fourierInv (MeasureTheory.MemLp.toLp W hW2))) : ℝ → ℂ) := by
  set m : ℝ → ℂ := fun ξ : ℝ => ∑ j ∈ Finset.range M, ε j *
        (starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P (2 ^ (j * 2 ^ i)) ξ)
         - starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P (2 ^ ((j + 1) * 2 ^ i)) ξ))
      with hmdef
  have hm_apply : ∀ ξ : ℝ, m ξ = ∑ j ∈ Finset.range M, ε j *
        (starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P (2 ^ (j * 2 ^ i)) ξ)
         - starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P (2 ^ ((j + 1) * 2 ^ i)) ξ)) := by
    intro ξ; rw [hmdef]
  have hW' : ∀ x : ℝ, FourierTransform.fourierInv (m * W) x
      = Work.BourgainPlan.Maximal.mstThetaOp P i M ε
          (fun y : ℝ => FourierTransform.fourierInv W y) x := by
    intro x
    rw [show (m * W) = (fun ξ : ℝ => (∑ j ∈ Finset.range M, ε j *
        (starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P (2 ^ (j * 2 ^ i)) ξ)
         - starRingEnd ℂ (Work.BourgainPlan.Maximal.polyProfile P (2 ^ ((j + 1) * 2 ^ i)) ξ))) * W ξ)
        from by ext ξ; simp only [Pi.mul_apply, hm_apply]]
    exact hW x
  exact ((multiplier_fourierInv_toLp_ae m hm W hW1 hW2).trans
    (Filter.Eventually.of_forall hW')).symm

end Work.BourgainPlan.Maximal
