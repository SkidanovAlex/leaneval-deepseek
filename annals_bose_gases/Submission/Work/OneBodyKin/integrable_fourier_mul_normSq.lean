import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Fourier.norm_fourier_le_of_integral_third_deriv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped ContDiff Topology Real FourierTransform

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The Fourier transform of an `L¹` function is bounded by the `L¹` norm of the function. -/
private lemma norm_fourier_le_integral_norm (f : ℝ³ → ℂ) (p : ℝ³) :
    ‖FourierTransform.fourier f p‖ ≤ ∫ z : ℝ³, ‖f z‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ ℝ³) f p

/-- Decay of the Fourier transform of a smooth compactly supported real function:
there is `C ≥ 0` with `‖𝓕 ψ p‖ ≤ C (1 + ‖p‖)⁻³`. -/
private lemma exists_fourier_decay {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ³,
      ‖FourierTransform.fourier (fun z : ℝ³ => (ψ z : ℂ)) p‖ ≤ C / (1 + ‖p‖) ^ 3 := by
  have hf3 : ContDiff ℝ 3 (fun z : ℝ³ => (ψ z : ℂ)) :=
    (hψ.of_le (WithTop.coe_le_coe.mpr le_top)).continuousLinearMap_comp Complex.ofRealCLM
  have hcsf : HasCompactSupport (fun z : ℝ³ => (ψ z : ℂ)) := by
    have h := hcs.comp_left (g := (Complex.ofRealCLM : ℝ → ℂ)) (by simp)
    simpa [Function.comp_def] using h
  set A : ℝ := max (∫ z : ℝ³, ‖(fun z : ℝ³ => (ψ z : ℂ)) z‖)
    (∫ z : ℝ³, ‖iteratedFDeriv ℝ 3 (fun z : ℝ³ => (ψ z : ℂ)) z‖) with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact le_trans (integral_nonneg (fun z => norm_nonneg _)) (le_max_left _ _)
  have h0 : (∫ z : ℝ³, ‖(fun z : ℝ³ => (ψ z : ℂ)) z‖) ≤ A := by
    rw [hA]; exact le_max_left _ _
  have h3 : (∫ z : ℝ³, ‖iteratedFDeriv ℝ 3 (fun z : ℝ³ => (ψ z : ℂ)) z‖) ≤ A := by
    rw [hA]; exact le_max_right _ _
  exact ⟨8 * A, by linarith, fun p =>
    Commons.Analysis.Fourier.norm_fourier_le_of_integral_third_deriv _ A hA0 hf3 hcsf h0 h3 p⟩

theorem integrable_fourier_mul_normSq {k ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hk : MeasureTheory.Integrable k) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (k z : ℂ)) p *
        ((‖FourierTransform.fourier (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) p‖ ^ 2 : ℝ) : ℂ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_fourier_decay hψ hcs
  set K : ℝ := ∫ z : ℝ³, ‖(k z : ℂ)‖ with hK
  have hK0 : 0 ≤ K := by rw [hK]; exact integral_nonneg (fun z => norm_nonneg _)
  have hkc : Integrable (fun z : ℝ³ => (k z : ℂ)) := hk.ofReal
  have hψc : Integrable (fun z : ℝ³ => (ψ z : ℂ)) := by
    have hcont : Continuous (fun z : ℝ³ => (ψ z : ℂ)) :=
      Complex.ofRealCLM.continuous.comp hψ.continuous
    refine hcont.integrable_of_hasCompactSupport ?_
    have h := hcs.comp_left (g := (Complex.ofRealCLM : ℝ → ℂ)) (by simp)
    simpa [Function.comp_def] using h
  have hkint : ∀ p : ℝ³, ‖FourierTransform.fourier (fun z : ℝ³ => (k z : ℂ)) p‖ ≤ K := by
    intro p
    rw [hK]
    exact norm_fourier_le_integral_norm (fun z : ℝ³ => (k z : ℂ)) p
  have hcontk : Continuous (fun p : ℝ³ =>
      FourierTransform.fourier (fun z : ℝ³ => (k z : ℂ)) p) :=
    VectorFourier.fourierIntegral_continuous (e := Real.fourierChar) (μ := volume)
      (L := innerₗ ℝ³) Real.continuous_fourierChar (innerSL ℝ).continuous₂ hkc
  have hcontψ : Continuous (fun p : ℝ³ =>
      FourierTransform.fourier (fun z : ℝ³ => (ψ z : ℂ)) p) :=
    VectorFourier.fourierIntegral_continuous (e := Real.fourierChar) (μ := volume)
      (L := innerₗ ℝ³) Real.continuous_fourierChar (innerSL ℝ).continuous₂ hψc
  have hg : Integrable (fun p : ℝ³ => K * C ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ))) := by
    have h1 : Integrable (fun p : ℝ³ => (1 + ‖p‖) ^ (-(6 : ℝ))) :=
      integrable_one_add_norm (E := ℝ³) (μ := volume) (r := 6) (by
        rw [finrank_euclideanSpace_fin]; norm_num)
    simpa using h1.const_mul (K * C ^ 2)
  have hmeas : AEStronglyMeasurable (fun p : ℝ³ =>
      FourierTransform.fourier (fun z : ℝ³ => (k z : ℂ)) p *
        ((‖FourierTransform.fourier (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2 : ℝ) : ℂ)) :=
    (hcontk.mul (Complex.ofRealCLM.continuous.comp ((hcontψ.norm).pow 2))).aestronglyMeasurable
  refine Integrable.mono' hg hmeas ?_
  filter_upwards with p
  have hdec : (C / (1 + ‖p‖) ^ 3) ^ 2 = C ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ)) := by
    have hu : (0 : ℝ) < 1 + ‖p‖ := by positivity
    have hA : (C / (1 + ‖p‖) ^ 3) ^ 2 = C ^ 2 * ((1 + ‖p‖) ^ 6)⁻¹ := by
      rw [div_pow, div_eq_mul_inv, show ((1 + ‖p‖) ^ 3) ^ 2 = (1 + ‖p‖) ^ 6 by ring]
    have hB : C ^ 2 * ((1 + ‖p‖) ^ 6)⁻¹ = C ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ)) := by
      rw [Real.rpow_neg hu.le (6 : ℝ)]
      exact congrArg (fun t => C ^ 2 * t⁻¹) (Real.rpow_natCast (1 + ‖p‖) 6).symm
    rw [hA, hB]
  have hψ2 : ‖FourierTransform.fourier (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2
      ≤ C ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ)) := by
    calc ‖FourierTransform.fourier (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2
        ≤ (C / (1 + ‖p‖) ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hC p) 2
      _ = C ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ)) := hdec
  have h2 : ‖(((‖FourierTransform.fourier (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2 : ℝ)) : ℂ)‖
      = ‖FourierTransform.fourier (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2 :=
    Complex.norm_of_nonneg (sq_nonneg _)
  rw [norm_mul, h2]
  calc ‖FourierTransform.fourier (fun z : ℝ³ => (k z : ℂ)) p‖ *
        ‖FourierTransform.fourier (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2
      ≤ K * (C ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ))) :=
        mul_le_mul (hkint p) hψ2 (sq_nonneg _) hK0
    _ = K * C ^ 2 * (1 + ‖p‖) ^ (-(6 : ℝ)) := by ring

end Work.OneBodyKin
