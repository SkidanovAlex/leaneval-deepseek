import Mathlib.Analysis.Fourier.LpSpace
import Submission.Commons.Analysis.Fourier.fourier_scaled_translate
import Submission.Commons.Analysis.Fourier.fourier_mul_support_of_integrable

namespace Commons.Analysis.Fourier

open MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace SchwartzMap ContDiff ENNReal

noncomputable section

private lemma continuous_modulation_factor {d : ℕ} (ℓ : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun x : EuclideanSpace ℝ (Fin d) =>
      Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x ℓ : ℝ) : ℂ))) := by
  fun_prop

private lemma modulation_factor_eq_char {d : ℕ} (ℓ x : EuclideanSpace ℝ (Fin d)) :
    Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x ℓ : ℝ) : ℂ))
      = ((Real.fourierChar (inner ℝ x ℓ) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply]
  push_cast
  ring_nf

private lemma norm_modulation_factor {d : ℕ} (ℓ x : EuclideanSpace ℝ (Fin d)) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x ℓ : ℝ) : ℂ))‖ = 1 := by
  rw [modulation_factor_eq_char ℓ x]; exact Circle.norm_coe _

private lemma modulation_factor_measurable {d : ℕ} (ℓ : EuclideanSpace ℝ (Fin d)) :
    AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin d) =>
      Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x ℓ : ℝ) : ℂ)))
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
  (continuous_modulation_factor ℓ).aestronglyMeasurable

theorem fourier_modulation_ae (d : ℕ) (ℓ : EuclideanSpace ℝ (Fin d))
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
    ∃ hf' : MeasureTheory.MemLp (fun x : EuclideanSpace ℝ (Fin d) =>
        Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x ℓ : ℝ) : ℂ)) * f x) 2
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      ((FourierTransform.fourier (hf'.toLp) : MeasureTheory.Lp ℂ 2
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
            EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[MeasureTheory.volume]
        (fun ξ : EuclideanSpace ℝ (Fin d) =>
          ((FourierTransform.fourier (hf.toLp) : MeasureTheory.Lp ℂ 2
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
              EuclideanSpace ℝ (Fin d) → ℂ) (ξ - ℓ)) := by
  have hf' : MeasureTheory.MemLp (fun x : EuclideanSpace ℝ (Fin d) =>
      Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x ℓ : ℝ) : ℂ)) * f x) 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
    refine hf.of_le ((modulation_factor_measurable ℓ).mul hf.1) ?_
    filter_upwards with x
    rw [norm_mul, norm_modulation_factor ℓ x, one_mul]
  refine ⟨hf', ?_⟩
  let F : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := hf.toLp f
  let G : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) :=
    hf'.toLp (fun x => Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x ℓ : ℝ) : ℂ)) * f x)
  have hmain : ((FourierTransform.fourier G : MeasureTheory.Lp ℂ 2
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
          EuclideanSpace ℝ (Fin d) → ℂ)
      =ᵐ[MeasureTheory.volume]
        (fun ξ : EuclideanSpace ℝ (Fin d) =>
          ((FourierTransform.fourier F : MeasureTheory.Lp ℂ 2
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
              EuclideanSpace ℝ (Fin d) → ℂ) (ξ - ℓ)) := by
    apply ae_eq_of_integral_contDiff_smul_eq
    · exact (MeasureTheory.Lp.memLp (FourierTransform.fourier G)).locallyIntegrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    · have hmp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) => x - ℓ)
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) := by
        simpa only [sub_eq_add_neg] using
          measurePreserving_add_right
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) (-ℓ)
      exact ((MeasureTheory.Lp.memLp (FourierTransform.fourier F)).comp_measurePreserving
        hmp).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    · intro ψ hψd hψs
      have hΦsupp : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin d) => (ψ x : ℂ)) :=
        hψs.comp_left (g := Complex.ofRealCLM) rfl
      have hΦdiff : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin d) => (ψ x : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp hψd
      let Φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ := hΦsupp.toSchwartzMap hΦdiff
      have hΦcoe : (Φ : EuclideanSpace ℝ (Fin d) → ℂ) = fun x => (ψ x : ℂ) := rfl
      have hΨsupp : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin d) => (ψ (y + ℓ) : ℂ)) :=
        hΦsupp.comp_homeomorph (Homeomorph.addRight ℓ)
      have hΨdiff : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin d) => (ψ (y + ℓ) : ℂ)) := by
        apply Complex.ofRealCLM.contDiff.comp
        exact hψd.comp (by fun_prop)
      let Ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ := hΨsupp.toSchwartzMap hΨdiff
      have hΨcoe : (Ψ : EuclideanSpace ℝ (Fin d) → ℂ) = fun y => (ψ (y + ℓ) : ℂ) := rfl
      have hΨshift : ∀ y : EuclideanSpace ℝ (Fin d),
          (FourierTransform.fourier Ψ : EuclideanSpace ℝ (Fin d) → ℂ) y
            = Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ y ℓ : ℝ) : ℂ)) *
              (FourierTransform.fourier Φ : EuclideanSpace ℝ (Fin d) → ℂ) y := by
        intro y
        have hΨeq : (Ψ : EuclideanSpace ℝ (Fin d) → ℂ)
            = fun x => (Φ : EuclideanSpace ℝ (Fin d) → ℂ) (x - (-ℓ)) := by
          funext x
          rw [hΨcoe, hΦcoe]
          simp
        rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, hΨeq]
        rw [fourier_comp_sub (Φ : EuclideanSpace ℝ (Fin d) → ℂ) (-ℓ) y]
        rw [show -(inner ℝ (-ℓ : EuclideanSpace ℝ (Fin d)) y) = inner ℝ y ℓ by
          rw [inner_neg_left, neg_neg, real_inner_comm]]
        rw [← modulation_factor_eq_char ℓ y, smul_eq_mul]
      have hLHS : ∫ x, ψ x • ((FourierTransform.fourier G : MeasureTheory.Lp ℂ 2
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
              EuclideanSpace ℝ (Fin d) → ℂ) x
          = ∫ x, (FourierTransform.fourier Φ : EuclideanSpace ℝ (Fin d) → ℂ) x *
              (Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x ℓ : ℝ) : ℂ)) * f x) := by
        calc ∫ x, ψ x • ((FourierTransform.fourier G : MeasureTheory.Lp ℂ 2 _) :
                EuclideanSpace ℝ (Fin d) → ℂ) x
            = ((FourierTransform.fourier G : MeasureTheory.Lp ℂ 2 _) :
                𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) Φ := by
                rw [Lp.toTemperedDistribution_apply]
                apply integral_congr_ae
                filter_upwards with x
                rw [hΦcoe]
                simp [Complex.real_smul]
          _ = ((G : MeasureTheory.Lp ℂ 2 _) : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))
                (FourierTransform.fourier Φ) := by
                rw [← Lp.fourier_toTemperedDistribution_eq G]
                exact TemperedDistribution.fourier_apply _ _
          _ = ∫ x, (FourierTransform.fourier Φ : EuclideanSpace ℝ (Fin d) → ℂ) x *
                (Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ x ℓ : ℝ) : ℂ)) * f x) := by
                rw [Lp.toTemperedDistribution_apply]
                apply integral_congr_ae
                filter_upwards [MeasureTheory.MemLp.coeFn_toLp hf'] with x hx
                rw [hx]
                rfl
      have hRHS : ∫ x, ψ x • ((FourierTransform.fourier F : MeasureTheory.Lp ℂ 2
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))) :
              EuclideanSpace ℝ (Fin d) → ℂ) (x - ℓ)
          = ∫ y, Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ y ℓ : ℝ) : ℂ)) *
              (FourierTransform.fourier Φ : EuclideanSpace ℝ (Fin d) → ℂ) y * f y := by
        calc ∫ x, ψ x • ((FourierTransform.fourier F : MeasureTheory.Lp ℂ 2 _) :
                EuclideanSpace ℝ (Fin d) → ℂ) (x - ℓ)
            = ∫ x, (Φ : EuclideanSpace ℝ (Fin d) → ℂ) x *
                ((FourierTransform.fourier F : MeasureTheory.Lp ℂ 2 _) :
                  EuclideanSpace ℝ (Fin d) → ℂ) (x - ℓ) := by
                apply integral_congr_ae
                filter_upwards with x
                rw [hΦcoe]
                simp [Complex.real_smul]
          _ = ∫ y, (Φ : EuclideanSpace ℝ (Fin d) → ℂ) (y + ℓ) *
                ((FourierTransform.fourier F : MeasureTheory.Lp ℂ 2 _) :
                  EuclideanSpace ℝ (Fin d) → ℂ) y := by
                rw [← integral_add_right_eq_self
                  (fun y : EuclideanSpace ℝ (Fin d) =>
                    (Φ : EuclideanSpace ℝ (Fin d) → ℂ) (y + ℓ) *
                    ((FourierTransform.fourier F : MeasureTheory.Lp ℂ 2 _) :
                      EuclideanSpace ℝ (Fin d) → ℂ) y) (-ℓ)]
                apply integral_congr_ae
                filter_upwards with x
                simp only [sub_eq_add_neg]
                rw [show x + -ℓ + ℓ = x by abel]
          _ = ((FourierTransform.fourier F : MeasureTheory.Lp ℂ 2 _) :
                𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) Ψ := by
                rw [Lp.toTemperedDistribution_apply]
                apply integral_congr_ae
                filter_upwards with y
                rw [hΨcoe, hΦcoe]
                simp
          _ = ((F : MeasureTheory.Lp ℂ 2 _) : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))
                (FourierTransform.fourier Ψ) := by
                rw [← Lp.fourier_toTemperedDistribution_eq F]
                exact TemperedDistribution.fourier_apply _ _
          _ = ∫ y, (FourierTransform.fourier Ψ : EuclideanSpace ℝ (Fin d) → ℂ) y * f y := by
                rw [Lp.toTemperedDistribution_apply]
                apply integral_congr_ae
                filter_upwards [MeasureTheory.MemLp.coeFn_toLp hf] with y hy
                rw [hy]
                rfl
          _ = ∫ y, Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ y ℓ : ℝ) : ℂ)) *
                (FourierTransform.fourier Φ : EuclideanSpace ℝ (Fin d) → ℂ) y * f y := by
                apply integral_congr_ae
                filter_upwards with y
                rw [hΨshift y]
      rw [hLHS, hRHS]
      apply integral_congr_ae
      filter_upwards with x
      ring
  exact hmain

end

end Commons.Analysis.Fourier