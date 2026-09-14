import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Filter
open scoped Topology ENNReal

lemma Measure_map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β) (he : MeasurePreserving (⇑e) μ ν)
    {ρ : α → ℝ≥0∞} (hρ : Measurable ρ) :
    Measure.map (⇑e) (μ.withDensity ρ) = ν.withDensity (ρ ∘ e.symm) := by
  classical
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply ρ (e.measurable hs),
      withDensity_apply (ρ ∘ e.symm) hs]
  rw [← lintegral_indicator (e.measurable hs) ρ,
      ← lintegral_indicator hs (ρ ∘ e.symm)]
  rw [← MeasurePreserving.lintegral_comp (MeasurePreserving.symm e he)
      (hρ.indicator (e.measurable hs))]
  congr 1
  ext b
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hb : b ∈ s
  · have hmem : ⇑e.symm b ∈ ⇑e ⁻¹' s := by
      simp only [Set.mem_preimage]; rwa [e.apply_symm_apply]
    rw [if_pos hmem, if_pos hb]
    rfl
  · have hmem : ⇑e.symm b ∉ ⇑e ⁻¹' s := by
      simp only [Set.mem_preimage]; rwa [e.apply_symm_apply]
    rw [if_neg hmem, if_neg hb]

lemma fderiv_comp_linearIsometryEquiv {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (ψ : F → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : E) (w : E) :
    (fderiv ℝ (ψ ∘ e) y) w = (fderiv ℝ ψ (e y)) (e w) := by
  have hdiff : HasFDerivAt ψ (fderiv ℝ ψ (e y)) (e y) :=
    ((hψ.contDiffAt).differentiableAt (by simp)).hasFDerivAt
  have hcomp : HasFDerivAt (ψ ∘ e) ((fderiv ℝ ψ (e y)).comp (e : E →L[ℝ] F)) y :=
    hdiff.comp y (ContinuousLinearMap.hasFDerivAt (e : E →L[ℝ] F))
  rw [hcomp.fderiv]
  rfl

lemma inner_toDual_symm_fderiv_comp {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (e : E ≃ₗᵢ[ℝ] F) (ψ : F → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : E) (w : E) :
    inner ℝ ((InnerProductSpace.toDual ℝ F).symm (fderiv ℝ ψ (e y))) (e w)
      = inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (ψ ∘ e) y)) w := by
  rw [InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply,
    fderiv_comp_linearIsometryEquiv e ψ hψ y w]

theorem weak_solution_const_of_weakGradient_transfer {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E]
    (hEucl : ∀ {n : ℕ} (f' g' : EuclideanSpace ℝ (Fin n) → ℝ)
      (G' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ 2 f' →
      AEStronglyMeasurable g' volume →
      Integrable (fun x => g' x ^ 2 * Real.exp (-(f' x))) volume →
      (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
        IntegrableOn (fun x => ‖G' x‖ ^ 2) K volume) →
      (∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        ∫ x, inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ ψ x)) (G' x)
          * Real.exp (-(f' x)) = 0) →
      (∀ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)),
        ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        ∫ x, ψ x * inner ℝ v (G' x) = -∫ x, (fderiv ℝ ψ x) v * g' x) →
      ∃ c : ℝ, g' =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-(f' x))))] fun _ => c)
    (f g : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hgmeas : AEStronglyMeasurable g volume)
    (hg2 : Integrable (fun x => g x ^ 2 * Real.exp (-(f x))) volume)
    (G : E → E)
    (hG1 : ∀ K : Set E, IsCompact K → IntegrableOn (fun x => ‖G x‖ ^ 2) K volume)
    (hG2 : ∀ ψ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ ψ x)) (G x)
        * Real.exp (-(f x)) = 0)
    (hG3 : ∀ (ψ : E → ℝ) (v : E), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, ψ x * inner ℝ v (G x) = -∫ x, (fderiv ℝ ψ x) v * g x) :
    ∃ c : ℝ, g =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-(f x))))] fun _ => c := by
  classical
  let n := Module.finrank ℝ E
  let e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := (stdOrthonormalBasis ℝ E).repr
  let f' : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f (e.symm x)
  let g' : EuclideanSpace ℝ (Fin n) → ℝ := fun x => g (e.symm x)
  let G' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => e (G (e.symm x))
  have hf' : ContDiff ℝ 2 f' := by
    change ContDiff ℝ 2 (fun x => f (e.symm x))
    exact hf.comp e.symm.contDiff
  have hgmeas' : AEStronglyMeasurable g' volume := by
    change AEStronglyMeasurable (fun x => g (e.symm x)) volume
    exact hgmeas.comp_measurePreserving (LinearIsometryEquiv.measurePreserving e.symm)
  have hg2' : Integrable (fun x : EuclideanSpace ℝ (Fin n) => g' x ^ 2 * Real.exp (-(f' x))) volume := by
    change Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      g (e.symm x) ^ 2 * Real.exp (-(f (e.symm x)))) volume
    exact (MeasurePreserving.integrable_comp
      (LinearIsometryEquiv.measurePreserving e.symm) hg2.aestronglyMeasurable).mpr hg2
  have hG1' : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      IntegrableOn (fun x => ‖G' x‖ ^ 2) K volume := by
    intro K hK
    have hK' : IsCompact (⇑(e.symm) '' K) := hK.image e.symm.continuous
    have hknown : IntegrableOn (fun y : E => ‖G y‖ ^ 2) (⇑(e.symm) '' K) volume := hG1 _ hK'
    have hiff := MeasurePreserving.integrableOn_comp_preimage
      (LinearIsometryEquiv.measurePreserving e.symm)
      (e.toMeasurableEquiv.symm).measurableEmbedding
      (f := fun y : E => ‖G y‖ ^ 2) (s := ⇑(e.symm) '' K)
    rw [Set.preimage_image_eq K e.symm.injective] at hiff
    have h2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => ‖G (e.symm x)‖ ^ 2) K volume :=
      hiff.mpr hknown
    have h3 : (fun x : EuclideanSpace ℝ (Fin n) => ‖G' x‖ ^ 2)
        = fun x => ‖G (e.symm x)‖ ^ 2 := by
      funext x
      simp only [G', e.norm_map]
    rw [h3]; exact h2
  have hG2' : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      ∫ x, inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
          (fderiv ℝ ψ x)) (G' x) * Real.exp (-(f' x)) = 0 := by
    intro ψ hψ hcψ
    have hψe : ContDiff ℝ (⊤ : ℕ∞) (ψ ∘ e) := hψ.comp e.contDiff
    have hcψe : HasCompactSupport (ψ ∘ e) := hcψ.comp_homeomorph e.toHomeomorph
    have hE := hG2 (ψ ∘ e) hψe hcψe
    let gE : E → ℝ := fun y => inner ℝ ((InnerProductSpace.toDual ℝ
      (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ ψ (e y))) (e (G y)) * Real.exp (-(f y))
    have h1 : (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ ((InnerProductSpace.toDual ℝ
        (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ ψ x)) (G' x) * Real.exp (-(f' x)))
        = fun x => gE (e.symm x) := by
      funext x
      simp only [gE, G', f', e.apply_symm_apply]
    rw [h1]
    have hcv := MeasurePreserving.integral_comp (f := ⇑(e.symm))
      (LinearIsometryEquiv.measurePreserving e.symm)
      (e.toMeasurableEquiv.symm).measurableEmbedding gE
    rw [hcv]
    have hgE : gE = fun y : E => inner ℝ ((InnerProductSpace.toDual ℝ E).symm
        (fderiv ℝ (ψ ∘ e) y)) (G y) * Real.exp (-(f y)) := by
      funext y
      simp only [gE]
      rw [inner_toDual_symm_fderiv_comp e ψ hψ y (G y)]
    rw [hgE]
    exact hE
  have hG3' : ∀ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, ψ x * inner ℝ v (G' x) = -∫ x, (fderiv ℝ ψ x) v * g' x := by
    intro ψ v hψ hcψ
    have hψe : ContDiff ℝ (⊤ : ℕ∞) (ψ ∘ e) := hψ.comp e.contDiff
    have hcψe : HasCompactSupport (ψ ∘ e) := hcψ.comp_homeomorph e.toHomeomorph
    have hE := hG3 (ψ ∘ e) (e.symm v) hψe hcψe
    have hL : (fun x : EuclideanSpace ℝ (Fin n) => ψ x * inner ℝ v (G' x))
        = fun x => (fun y : E => (ψ ∘ e) y * inner ℝ (e.symm v) (G y)) (e.symm x) := by
      funext x
      simp only [G', Function.comp_apply, e.apply_symm_apply]
      congr 1
      rw [← e.inner_map_map (e.symm v) (G (e.symm x)), e.apply_symm_apply]
    have hR : (fun x : EuclideanSpace ℝ (Fin n) => (fderiv ℝ ψ x) v * g' x)
        = fun x => (fun y : E => (fderiv ℝ (ψ ∘ e) y) (e.symm v) * g y) (e.symm x) := by
      funext x
      simp only [g']
      congr 1
      rw [fderiv_comp_linearIsometryEquiv e ψ hψ (e.symm x) (e.symm v), e.apply_symm_apply,
        e.apply_symm_apply]
    rw [hL, hR]
    have hcvL := MeasurePreserving.integral_comp (f := ⇑(e.symm))
      (LinearIsometryEquiv.measurePreserving e.symm)
      (e.toMeasurableEquiv.symm).measurableEmbedding
      (fun y : E => (ψ ∘ e) y * inner ℝ (e.symm v) (G y))
    have hcvR := MeasurePreserving.integral_comp (f := ⇑(e.symm))
      (LinearIsometryEquiv.measurePreserving e.symm)
      (e.toMeasurableEquiv.symm).measurableEmbedding
      (fun y : E => (fderiv ℝ (ψ ∘ e) y) (e.symm v) * g y)
    rw [hcvL, hcvR]
    exact hE
  obtain ⟨c, hc⟩ := hEucl f' g' G' hf' hgmeas' hg2' hG1' hG2' hG3'
  refine ⟨c, ?_⟩
  set ρ : E → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-(f y))) with hρ
  change g =ᵐ[(volume : Measure E).withDensity ρ] fun _ => c
  have hρmeas : Measurable ρ := by
    rw [hρ]
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (hf.continuous.neg.measurable))
  have hcmap : Measure.map (⇑e) ((volume : Measure E).withDensity ρ)
      = (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (fun x => ENNReal.ofReal (Real.exp (-(f' x)))) :=
    Measure_map_withDensity_equiv e.toMeasurableEquiv
      (LinearIsometryEquiv.measurePreserving e) hρmeas
  have hmp : MeasurePreserving (⇑e) ((volume : Measure E).withDensity ρ)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(f' x))))) :=
    ⟨(LinearIsometryEquiv.measurePreserving e).measurable, hcmap⟩
  have hzero : ((volume : Measure E).withDensity ρ) {x | g x ≠ c} = 0 := by
    have hset : {x : E | g x ≠ c}
        = ⇑e ⁻¹' {y : EuclideanSpace ℝ (Fin n) | g' y ≠ c} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, g', e.symm_apply_apply]
    rw [hset]
    refine hmp.preimage_null ?_
    have hh : (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(f' x)))) {y | g' y ≠ c} = 0 := by
      have := ae_iff.1 (show ∀ᵐ y ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
          (fun x => ENNReal.ofReal (Real.exp (-(f' x))))), g' y = c from hc)
      simpa using this
    exact hh
  show ∀ᵐ x ∂((volume : Measure E).withDensity ρ), g x = c
  rw [ae_iff]
  exact hzero


end Commons.Analysis.GaussianMeasure