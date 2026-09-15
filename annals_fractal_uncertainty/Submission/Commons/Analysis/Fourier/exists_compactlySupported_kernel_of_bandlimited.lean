import Mathlib.Analysis.Fourier.LpSpace
import Submission.Commons.Analysis.Fourier.eLpNorm_one_le_of_ae_support_cube

namespace Commons.Analysis.Fourier

open MeasureTheory FourierTransform
open scoped ENNReal

noncomputable section

/-- On `L²`, the inverse Fourier transform is the Fourier transform composed with negation:
`𝓕⁻ f x = 𝓕 f (-x)`, as an identity of `L²` functions.  This is the `L²` counterpart of
`Real.fourierInv_eq_fourier_neg`; it is proved by density of the Schwartz functions in `L²`. -/
theorem fourierInv_eq_compMeasurePreserving_neg (d : ℕ)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    𝓕⁻ f = Lp.compMeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) => -x)
      (Measure.measurePreserving_neg (volume : Measure (EuclideanSpace ℝ (Fin d)))) (𝓕 f) := by
  have hdense := SchwartzMap.denseRange_toLpCLM (E := EuclideanSpace ℝ (Fin d)) (F := ℂ) (p := 2)
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (by norm_num)
  refine DenseRange.induction_on hdense f ?_ ?_
  · refine isClosed_eq ?_ ?_
    · exact continuous_fourierInv
    · exact ((Lp.isometry_compMeasurePreserving
        (Measure.measurePreserving_neg (volume : Measure (EuclideanSpace ℝ (Fin d))))).continuous).comp
        continuous_fourier
  · intro g
    simp only [SchwartzMap.toLpCLM_apply]
    rw [SchwartzMap.toLp_fourierInv_eq, SchwartzMap.toLp_fourier_eq]
    have hrw : (𝓕 g).toLp 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))
        = MemLp.toLp (fun x => (𝓕 g) x)
            ((𝓕 g).memLp 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) := rfl
    rw [hrw, Lp.toLp_compMeasurePreserving]
    apply MemLp.toLp_congr
    filter_upwards with x
    simp only [Function.comp_apply]
    rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe]
    exact Real.fourierInv_eq_fourier_neg (g : EuclideanSpace ℝ (Fin d) → ℂ) x

theorem exists_compactlySupported_kernel_of_bandlimited (d : ℕ)
    (ψ : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (r : ℝ) (hr : 0 < r)
    (hsupp : ∀ᵐ ξ ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      (∃ i : Fin d, r < |ξ i|) →
      ((FourierTransform.fourier ψ : MeasureTheory.Lp ℂ 2
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
          EuclideanSpace ℝ (Fin d) → ℂ) ξ = 0) :
    ∃ φ : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      FourierTransform.fourier φ = ψ ∧
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
        (∃ i : Fin d, r < |x i|) → (φ : EuclideanSpace ℝ (Fin d) → ℂ) x = 0) ∧
      MeasureTheory.MemLp (φ : EuclideanSpace ℝ (Fin d) → ℂ) 1
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) ∧
      (MeasureTheory.eLpNorm (φ : EuclideanSpace ℝ (Fin d) → ℂ) 1
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))).toReal ≤
        (2 * r) ^ ((d : ℝ) / 2) * ‖ψ‖ := by
  have hrefl := fourierInv_eq_compMeasurePreserving_neg d ψ
  -- pull back the band-limit hypothesis along the measure-preserving map `x ↦ -x`
  have hpull : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      (∃ i : Fin d, r < |(-x) i|) →
        ((𝓕 ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
          EuclideanSpace ℝ (Fin d) → ℂ) (-x) = 0 :=
    (Measure.measurePreserving_neg (volume : Measure (EuclideanSpace ℝ (Fin d)))).quasiMeasurePreserving.tendsto_ae.eventually
      hsupp
  have hcoe : ((𝓕⁻ ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
        EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[volume]
      fun x => ((𝓕 ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
        EuclideanSpace ℝ (Fin d) → ℂ) (-x) := by
    rw [hrefl]
    filter_upwards [Lp.coeFn_compMeasurePreserving (𝓕 ψ)
      (Measure.measurePreserving_neg (volume : Measure (EuclideanSpace ℝ (Fin d))))] with x hx
    rw [hx]
    simp only [Function.comp_apply]
  have hsuppφ : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      (∃ i : Fin d, r < |x i|) →
        ((𝓕⁻ ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
          EuclideanSpace ℝ (Fin d) → ℂ) x = 0 := by
    filter_upwards [hcoe, hpull] with x hx hpx hcon
    rw [hx, hpx (by simpa [Pi.neg_apply] using hcon)]
  obtain ⟨h1, hbound⟩ := eLpNorm_one_le_of_ae_support_cube d r hr
    (Lp.memLp (𝓕⁻ ψ)) hsuppφ
  refine ⟨𝓕⁻ ψ, fourier_fourierInv_eq ψ, hsuppφ, h1, ?_⟩
  calc (eLpNorm ((𝓕⁻ ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
          EuclideanSpace ℝ (Fin d) → ℂ) 1 (volume : Measure (EuclideanSpace ℝ (Fin d)))).toReal
      ≤ (2 * r) ^ ((d : ℝ) / 2) *
          (eLpNorm ((𝓕⁻ ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) 2
            (volume : Measure (EuclideanSpace ℝ (Fin d)))).toReal := hbound
    _ = (2 * r) ^ ((d : ℝ) / 2) * ‖ψ‖ := by
        congr 1
        rw [← Lp.norm_def (𝓕⁻ ψ), ← MeasureTheory.Lp.norm_fourier_eq (𝓕⁻ ψ), fourier_fourierInv_eq]

end

end Commons.Analysis.Fourier