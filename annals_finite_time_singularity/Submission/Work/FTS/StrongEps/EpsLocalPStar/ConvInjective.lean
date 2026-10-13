import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Tactic.Have
import Mathlib.Topology.UniformSpace.Uniformizable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology FourierTransform ContDiff SchwartzMap
open MeasureTheory Set Filter

/-- A continuous real function vanishing off `[-1,1]` is integrable. -/
private lemma integrable_of_continuous_compactSupport {ρ : ℝ → ℝ} (hρc : Continuous ρ)
    (hρs : ∀ x ∉ Set.Icc (-1 : ℝ) 1, ρ x = 0) : Integrable ρ :=
  hρc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc
      (fun x hx => by by_contra h; exact hx (hρs x (by simpa using h))))

/-- **Injectivity of the convolution with a compactly supported kernel of nonvanishing
Fourier transform.**  If `ρ : ℝ → ℝ` is continuous, supported in `[-1,1]`, and its (complex)
Fourier transform is nonzero almost everywhere, then `ρ * f = 0` forces `f = 0` a.e. -/
theorem ConvInjective {ρ f : ℝ → ℝ} (hρc : Continuous ρ)
    (hρs : ∀ x ∉ Set.Icc (-1 : ℝ) 1, ρ x = 0) (hρ0 : (∫ x, ρ x) ≠ 0)
    (hF : ∀ᵐ ξ ∂MeasureTheory.volume, 𝓕 (fun x : ℝ => (ρ x : ℂ)) ξ ≠ 0)
    (hf : MeasureTheory.Integrable f)
    (hconv : ∀ u : ℝ, ∫ s, ρ (u - s) * f s = 0) :
    f =ᵐ[MeasureTheory.volume] 0 := by
  -- integrability of the involved functions
  have hρ_int : Integrable ρ := integrable_of_continuous_compactSupport hρc hρs
  have hρℂ : Integrable (fun x : ℝ => (ρ x : ℂ)) := hρ_int.ofReal
  have hfℂ : Integrable (fun x : ℝ => (f x : ℂ)) := hf.ofReal
  -- the convolution `ρ * f` vanishes identically
  have hconv_zero : convolution (fun x : ℝ => (ρ x : ℂ)) (fun x : ℝ => (f x : ℂ))
      (ContinuousLinearMap.mul ℂ ℂ) volume = 0 := by
    funext u
    rw [convolution_def]
    have h1 : (fun t : ℝ => (ContinuousLinearMap.mul ℂ ℂ) (ρ t) (f (u - t))) =
        fun t => ((ρ t * f (u - t) : ℝ) : ℂ) := by
      funext t; rw [Complex.ofReal_mul]; rfl
    rw [h1, integral_complex_ofReal]
    have h2 : (∫ t : ℝ, ρ t * f (u - t)) = ∫ s : ℝ, ρ (u - s) * f s := by
      have := integral_sub_left_eq_self (fun t : ℝ => ρ t * f (u - t)) volume u
      simpa using this.symm
    rw [h2, hconv u]
    simp
  -- hence the Fourier transform of `ρ` times that of `f` vanishes everywhere
  have hprod : ∀ ξ : ℝ, 𝓕 (fun x : ℝ => (ρ x : ℂ)) ξ * 𝓕 (fun x : ℝ => (f x : ℂ)) ξ = 0 := by
    intro ξ
    rw [← Real.fourier_mul_convolution_eq (f₁ := fun x : ℝ => (ρ x : ℂ))
      (f₂ := fun x : ℝ => (f x : ℂ)) hρℂ hfℂ ξ, hconv_zero]
    simp [Real.fourier_eq]
  -- so the Fourier transform of `f` vanishes almost everywhere
  have hzero : (fun ξ => 𝓕 (fun x : ℝ => (f x : ℂ)) ξ) =ᵐ[MeasureTheory.volume] 0 := by
    filter_upwards [hF] with ξ hξ
    exact (mul_eq_zero.mp (hprod ξ)).resolve_left hξ
  -- it remains to deduce `f = 0` a.e., by duality against compactly supported smooth tests
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable ?_
  intro ψ hψ hψc
  let Ψ : 𝓢(ℝ, ℂ) := (hψc.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)).toSchwartzMap
    (ContDiff.comp (ContinuousLinearMap.contDiff Complex.ofRealCLM) hψ)
  have hΨcoe : (Ψ : ℝ → ℂ) = fun x => (ψ x : ℂ) := by
    ext x; simp [Ψ]
  let g₀ : 𝓢(ℝ, ℂ) := 𝓕⁻ Ψ
  have hg₀ : (𝓕 (g₀ : ℝ → ℂ)) = fun x => (ψ x : ℂ) := by
    rw [← SchwartzMap.fourier_coe g₀, show 𝓕 g₀ = Ψ from FourierInvPair.fourier_fourierInv_eq Ψ]
    exact hΨcoe
  -- the Fourier duality identity `∫ f 𝓕 g = ∫ 𝓕 f g`
  have hdual : ∫ x, (f x : ℂ) • (𝓕 (g₀ : ℝ → ℂ)) x =
      ∫ ξ, (𝓕 (fun x : ℝ => (f x : ℂ))) ξ • (g₀ : ℝ → ℂ) ξ := by
    have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.lsmul ℂ ℂ)
      (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hfℂ
      (SchwartzMap.integrable (μ := volume) g₀)
    simpa [ContinuousLinearMap.lsmul_apply, VectorFourier.fourierIntegral, Real.fourier_eq,
      LinearMap.flip_apply] using h.symm
  have hrhs : ∫ ξ, (𝓕 (fun x : ℝ => (f x : ℂ))) ξ • (g₀ : ℝ → ℂ) ξ = 0 := by
    have : (fun ξ => (𝓕 (fun x : ℝ => (f x : ℂ))) ξ • (g₀ : ℝ → ℂ) ξ) =ᵐ[volume] 0 := by
      filter_upwards [hzero] with ξ hξ
      simp [hξ]
    rw [integral_congr_ae this]
    simp
  have key : ((∫ x : ℝ, f x * ψ x : ℝ) : ℂ) = 0 := by
    rw [← integral_complex_ofReal]
    calc ∫ x, ((f x * ψ x : ℝ) : ℂ) = ∫ x, (f x : ℂ) • (𝓕 (g₀ : ℝ → ℂ)) x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hg₀]
          simp [Complex.ofReal_mul, smul_eq_mul]
      _ = 0 := by rw [hdual, hrhs]
  have key2 : ∫ x : ℝ, f x * ψ x = 0 := by
    have := key
    rwa [Complex.ofReal_eq_zero] at this
  rw [show (∫ x : ℝ, ψ x • f x) = ∫ x : ℝ, f x * ψ x from by
    apply integral_congr_ae; filter_upwards with x; simp [smul_eq_mul, mul_comm]]
  exact key2

end Work.FTS.StrongEps.EpsLocalPStar
