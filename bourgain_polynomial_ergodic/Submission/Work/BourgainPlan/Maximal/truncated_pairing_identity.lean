import Mathlib
import Submission.Work.Analysis.Fourier.band_projection_schwartz_lp
import Submission.Work.BourgainPlan.Maximal.plancherel_fourier_inner
import Submission.Work.BourgainPlan.Maximal.integral_inner_fourierInv_eq
import Submission.Work.BourgainPlan.Maximal.integral_inner_fourierInv_fourierInv_eq
import Submission.Work.BourgainPlan.Maximal.integrable_memLp2_mul_fourierSchwartz

namespace Work.BourgainPlan.Maximal

open MeasureTheory FourierTransform
open scoped FourierTransform ComplexInnerProductSpace

/-- For `g ∈ L¹(ℝ, ℂ)` the truncated Fourier transform `ξ ↦ 1_{(a,b)}(ξ) * 𝓕g(ξ)` belongs to
`L¹ ∩ L²`: it is bounded by `‖g‖₁` and supported on the finite measure interval `(a,b)`. -/
lemma integrable_memLp2_truncatedFourier_of_integrable {a b : ℝ} {g : ℝ → ℂ}
    (hg : MeasureTheory.Integrable g) :
    MeasureTheory.Integrable
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0) * FourierTransform.fourier g ξ)
      ∧ MeasureTheory.MemLp
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0) * FourierTransform.fourier g ξ) 2
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Ioo a b) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hcont : Continuous (FourierTransform.fourier g) :=
    VectorFourier.fourierIntegral_continuous (e := Real.fourierChar)
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (L := innerₗ ℝ) (f := g)
      Real.continuous_fourierChar continuous_inner hg
  set C : ℝ := ∫ v : ℝ, ‖g v‖ with hC
  have hbound : ∀ ξ : ℝ,
      ‖(if ξ ∈ Set.Ioo a b then (1:ℂ) else 0) * FourierTransform.fourier g ξ‖
        ≤ C * ‖(Set.Ioo a b).indicator (fun _ => (1:ℂ)) ξ‖ := by
    intro ξ
    by_cases h : ξ ∈ Set.Ioo a b
    · rw [if_pos h, Set.indicator_of_mem h, norm_one, one_mul, hC, mul_one]
      exact VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar
        MeasureTheory.volume (innerₗ ℝ) g ξ
    · rw [if_neg h, Set.indicator_of_notMem h, zero_mul, norm_zero, mul_zero]
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0) * FourierTransform.fourier g ξ)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    ((Measurable.ite measurableSet_Ioo measurable_const measurable_const).aestronglyMeasurable).mul
      hcont.aestronglyMeasurable
  exact ⟨MeasureTheory.memLp_one_iff_integrable.mp
          (MeasureTheory.MemLp.of_le_mul
            (MeasureTheory.memLp_indicator_const 1 measurableSet_Ioo (1:ℂ) (Or.inr hvol))
            hmeas (ae_of_all _ hbound)),
        MeasureTheory.MemLp.of_le_mul
          (MeasureTheory.memLp_indicator_const 2 measurableSet_Ioo (1:ℂ) (Or.inr hvol))
          hmeas (ae_of_all _ hbound)⟩

theorem truncated_pairing_identity {m : ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hm : ∀ ξ : ℝ, ‖m ξ‖ ≤ A) (hmm : MeasureTheory.AEStronglyMeasurable m MeasureTheory.volume)
    {a b : ℝ} (hab : a < b)
    (G : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (hg : MeasureTheory.Integrable g) :
    (∫ x : ℝ, inner ℂ (FourierTransformInv.fourierInv
        (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0)
          * FourierTransform.fourier (G : ℝ → ℂ) ξ) x) (g x))
      = star (∫ x : ℝ, inner ℂ (FourierTransformInv.fourierInv
          (fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0)
            * FourierTransform.fourier g ξ) x) (FourierTransformInv.fourierInv
          (fun ξ : ℝ => m ξ * FourierTransform.fourier (G : ℝ → ℂ) ξ) x)) := by
  set F : ℝ → ℂ :=
    fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then m ξ else 0) * FourierTransform.fourier (G : ℝ → ℂ) ξ
    with hF
  set H : ℝ → ℂ :=
    fun ξ : ℝ => (if ξ ∈ Set.Ioo a b then (1:ℂ) else 0) * FourierTransform.fourier g ξ with hH
  set K : ℝ → ℂ := fun ξ : ℝ => m ξ * FourierTransform.fourier (G : ℝ → ℂ) ξ with hK
  -- side conditions
  have hNmeas : MeasureTheory.AEStronglyMeasurable
      (fun ξ : ℝ => if ξ ∈ Set.Ioo a b then m ξ else 0) MeasureTheory.volume := by
    have h1 : (fun ξ : ℝ => if ξ ∈ Set.Ioo a b then m ξ else 0)
        = (Set.Ioo a b).indicator m := by
      funext ξ; rw [Set.indicator_apply]
    rw [h1]
    exact hmm.indicator measurableSet_Ioo
  have hNA : ∀ ξ : ℝ, ‖(fun ξ : ℝ => if ξ ∈ Set.Ioo a b then m ξ else 0) ξ‖ ≤ A := by
    intro ξ
    by_cases h : ξ ∈ Set.Ioo a b
    · simpa only [h, ↓reduceIte] using hm ξ
    · simpa only [h, ↓reduceIte, norm_zero] using hA
  have hFint : MeasureTheory.Integrable F := by
    rw [hF]
    exact (integrable_memLp2_mul_fourierSchwartz
      (fun ξ : ℝ => if ξ ∈ Set.Ioo a b then m ξ else 0) A hNmeas hNA G).1
  have hKint : MeasureTheory.Integrable K := by
    rw [hK]
    exact (integrable_memLp2_mul_fourierSchwartz m A hmm hm G).1
  have hK2 : MeasureTheory.MemLp K 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    rw [hK]
    exact (integrable_memLp2_mul_fourierSchwartz m A hmm hm G).2
  have hHint : MeasureTheory.Integrable H := by
    rw [hH]
    exact (integrable_memLp2_truncatedFourier_of_integrable hg).1
  have hH2 : MeasureTheory.MemLp H 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    rw [hH]
    exact (integrable_memLp2_truncatedFourier_of_integrable hg).2
  -- pointwise identity of the two integrands
  have hpt : ∀ ξ : ℝ,
      inner ℂ (F ξ) (FourierTransform.fourier g ξ) = star (inner ℂ (H ξ) (K ξ)) := by
    intro ξ
    simp only [hF, hH, hK]
    rw [RCLike.inner_apply, RCLike.inner_apply]
    by_cases h : ξ ∈ Set.Ioo a b
    · simp only [h, ↓reduceIte, starRingEnd_apply, star_mul, star_star, one_mul]
    · simp only [h, ↓reduceIte, starRingEnd_apply, star_zero, mul_zero, zero_mul]
  -- the two pairing identities
  have h1 := integral_inner_fourierInv_eq F g hFint hg
  have h2 := integral_inner_fourierInv_fourierInv_eq H K hHint hH2 hKint hK2
  calc (∫ x : ℝ, inner ℂ (FourierTransformInv.fourierInv F x) (g x))
      = ∫ x : ℝ, inner ℂ (F x) (FourierTransform.fourier g x) := h1
    _ = ∫ x : ℝ, star (inner ℂ (H x) (K x)) := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpt x
    _ = star (∫ x : ℝ, inner ℂ (H x) (K x)) := integral_conj
    _ = star (∫ x : ℝ, inner ℂ (FourierTransformInv.fourierInv H x)
            (FourierTransformInv.fourierInv K x)) := by rw [← h2]

end Work.BourgainPlan.Maximal
