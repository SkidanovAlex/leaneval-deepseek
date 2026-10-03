import Mathlib
import Submission.Work.Analysis.IWMultiplier.Defs
import Submission.Port.Aesm

/-!
# Translating the symbol of the continuous Fourier multiplier

`Work.Analysis.IWMultiplier.IsLqMultiplierBound p φ M` says that the Fourier multiplier
`T_φ = 𝓕⁻ ∘ (φ · 𝓕)` with symbol `φ` is bounded by `M` on `L^p(ℝ)` (tested on Schwartz
functions).  This file shows that the bound is invariant under translating the symbol,
`φ ↦ (ξ ↦ φ (ξ + b))`: this is the multiplication-formulation counterpart of the fact that the
convolution kernel `𝓕⁻φ` may be modulated by a unimodular function without changing its `L^p`
behaviour.

The proof conjugates `T_{φ(·+b)}` by the modulation `M_b : f ↦ (x ↦ 𝐞(b x) f x)`, which is an
isometry of every `L^p` (and preserves the Schwartz space: it is the inverse Fourier transform of
the translation `ξ ↦ ξ - b` of the symbol).  The two Fourier-analytic inputs are

* `fourierInv_comp_add` — the inverse transform of the translate `ξ ↦ Ψ (ξ + b)` is the
  modulation of `𝓕⁻Ψ` by `𝐞(-b ·)`;
* `modSchwartz_fourier`, `modSchwartz_apply` — the modulated Schwartz function and its transform.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTAreas.SupNorm

open scoped FourierTransform ENNReal NNReal
open MeasureTheory

/-- **The inverse Fourier transform of a translate.**  Translating the argument of the function
being transformed by `b` multiplies the inverse Fourier transform by the character
`𝐞(-b ·)`. -/
theorem fourierInv_comp_add (Ψ : ℝ → ℂ) (b x : ℝ) :
    𝓕⁻ (fun ξ => Ψ (ξ + b)) x = (Real.fourierChar (-(b * x)) : ℂ) * 𝓕⁻ Ψ x := by
  change VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ ℝ)
      (Ψ ∘ fun v => v + b) x = _
  rw [VectorFourier.fourierIntegral_comp_add_right]
  dsimp only
  have harg : (-innerₗ ℝ) b x = -(b * x) := by
    simp only [LinearMap.neg_apply, innerₗ_apply_apply]
    simp
    ring
  rw [Circle.smul_def, smul_eq_mul, harg]
  rfl

/-- **The inverse Fourier transform of a translate, opposite sign.**  Translating the argument of
the function being transformed by `-b` multiplies the inverse Fourier transform by `𝐞(b ·)`. -/
theorem fourierInv_comp_sub (Ψ : ℝ → ℂ) (b x : ℝ) :
    𝓕⁻ (fun ξ => Ψ (ξ - b)) x = (Real.fourierChar (b * x) : ℂ) * 𝓕⁻ Ψ x := by
  have h := fourierInv_comp_add Ψ (-b) x
  simpa [sub_eq_add_neg] using h

/-- The modulation `x ↦ 𝐞(b x) f x` of a Schwartz function `f`, realised through the Fourier
transform as the inverse Fourier transform of the translate `ξ ↦ 𝓕f (ξ - b)` of `𝓕f`. -/
noncomputable def modSchwartz (f : SchwartzMap ℝ ℂ) (b : ℝ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ ((𝓕 f).compSubConstCLM ℂ b)

/-- The Fourier transform of the modulation of `f` is the translate of `𝓕f`. -/
theorem modSchwartz_fourier (f : SchwartzMap ℝ ℂ) (b : ℝ) :
    𝓕 ((modSchwartz f b : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun η => 𝓕 (f : ℝ → ℂ) (η - b) := by
  have hkey : 𝓕 (𝓕⁻ (((𝓕 f).compSubConstCLM ℂ b) : ℝ → ℂ))
      = (((𝓕 f).compSubConstCLM ℂ b) : ℝ → ℂ) :=
    Continuous.fourier_fourierInv_eq ((𝓕 f).compSubConstCLM ℂ b).continuous
      ((𝓕 f).compSubConstCLM ℂ b).integrable
      (by simpa only [SchwartzMap.fourier_coe] using
        (𝓕 ((𝓕 f).compSubConstCLM ℂ b)).integrable)
  calc 𝓕 ((modSchwartz f b : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = 𝓕 (𝓕⁻ (((𝓕 f).compSubConstCLM ℂ b) : ℝ → ℂ)) := by
        rw [modSchwartz, SchwartzMap.fourierInv_coe]
    _ = (((𝓕 f).compSubConstCLM ℂ b) : ℝ → ℂ) := hkey
    _ = fun η => 𝓕 (f : ℝ → ℂ) (η - b) := by
        funext η
        rw [SchwartzMap.compSubConstCLM_apply, SchwartzMap.fourier_coe]

/-- The modulation of a Schwartz function: pointwise values. -/
theorem modSchwartz_apply (f : SchwartzMap ℝ ℂ) (b x : ℝ) :
    (modSchwartz f b : ℝ → ℂ) x = (Real.fourierChar (b * x) : ℂ) * f x := by
  have hg : 𝓕⁻ (𝓕 ((modSchwartz f b : SchwartzMap ℝ ℂ) : ℝ → ℂ))
      = (modSchwartz f b : ℝ → ℂ) :=
    Continuous.fourierInv_fourier_eq (modSchwartz f b).continuous (modSchwartz f b).integrable
      (by simpa only [SchwartzMap.fourier_coe] using (𝓕 (modSchwartz f b)).integrable)
  have hf : 𝓕⁻ (𝓕 (f : ℝ → ℂ)) = (f : ℝ → ℂ) :=
    Continuous.fourierInv_fourier_eq f.continuous f.integrable
      (by simpa only [SchwartzMap.fourier_coe] using (𝓕 f).integrable)
  calc (modSchwartz f b : ℝ → ℂ) x
      = 𝓕⁻ (𝓕 ((modSchwartz f b : SchwartzMap ℝ ℂ) : ℝ → ℂ)) x := by rw [hg]
    _ = 𝓕⁻ (fun η => 𝓕 (f : ℝ → ℂ) (η - b)) x := by rw [modSchwartz_fourier]
    _ = (Real.fourierChar (b * x) : ℂ) * 𝓕⁻ (𝓕 (f : ℝ → ℂ)) x := fourierInv_comp_sub _ b x
    _ = (Real.fourierChar (b * x) : ℂ) * f x := by rw [hf]

/-- The complex number `𝐞 t` has norm one. -/
theorem norm_fourierChar (t : ℝ) : ‖(Real.fourierChar t : ℂ)‖ = 1 := by
  rw [Real.fourierChar_apply, Complex.norm_exp]
  simp

/-- `contMulOp φ f` is continuous for *every* symbol: if `φ · 𝓕 f` is integrable this is the
continuity of the Fourier integral, and otherwise the defining integral is `0` everywhere. -/
private lemma contMulOp_continuous_any (φ f : ℝ → ℂ) :
    Continuous (Work.Analysis.IWMultiplier.contMulOp φ f) := by
  rw [Work.Analysis.IWMultiplier.contMulOp, Real.fourierInv_eq_fourier_comp_neg]
  by_cases hg : Integrable (fun ξ : ℝ => φ (-ξ) * 𝓕 f (-ξ))
  · exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg
  · have h0 : 𝓕 (fun ξ : ℝ => φ (-ξ) * 𝓕 f (-ξ)) = fun _ => 0 := by
      funext w
      show VectorFourier.fourierIntegral _ _ _ _ w = 0
      rw [VectorFourier.fourierIntegral]
      exact integral_undef (mt (VectorFourier.fourierIntegral_convergent_iff
        Real.continuous_fourierChar (innerSL ℝ).continuous₂ w).1 hg)
    rw [h0]; exact continuous_const

open Work.Analysis.IWMultiplier in
theorem IsLqMultiplierBound_comp_add {p : ENNReal} (hp1 : 1 ≤ p) (hp2 : p < ⊤)
    {φ : ℝ → ℂ} {M : NNReal}
    (h : Work.Analysis.IWMultiplier.IsLqMultiplierBound p φ M) (b : ℝ) :
    Work.Analysis.IWMultiplier.IsLqMultiplierBound p (fun ξ => φ (ξ + b)) M := by
  intro f
  -- the modulation of `f` has the same `L^p` seminorm as `f`
  have hgnorm : eLpNorm ((modSchwartz f b : SchwartzMap ℝ ℂ) : ℝ → ℂ) p volume
      = eLpNorm (f : ℝ → ℂ) p volume := by
    apply eLpNorm_congr_norm_ae (hf := by pw_aesm) (hg := by pw_aesm)
    filter_upwards with x
    rw [modSchwartz_apply, norm_mul, norm_fourierChar, one_mul]
  -- the two multipliers differ by a unimodular factor
  have hpoint : ∀ x, contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ) x
      = (Real.fourierChar (-(b * x)) : ℂ)
          * contMulOp φ ((modSchwartz f b : SchwartzMap ℝ ℂ) : ℝ → ℂ) x := by
    intro x
    have hfun₁ : (fun ξ => φ (ξ + b) * 𝓕 (f : ℝ → ℂ) ξ)
        = fun ξ => (fun η => φ η * 𝓕 (f : ℝ → ℂ) (η - b)) (ξ + b) := by
      funext ξ
      simp
    have hfun₂ : (fun η => φ η * 𝓕 (f : ℝ → ℂ) (η - b))
        = fun η => φ η * 𝓕 ((modSchwartz f b : SchwartzMap ℝ ℂ) : ℝ → ℂ) η := by
      funext η
      rw [modSchwartz_fourier]
    calc contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ) x
        = 𝓕⁻ (fun ξ => φ (ξ + b) * 𝓕 (f : ℝ → ℂ) ξ) x := rfl
      _ = 𝓕⁻ (fun ξ => (fun η => φ η * 𝓕 (f : ℝ → ℂ) (η - b)) (ξ + b)) x := by
            rw [hfun₁]
      _ = (Real.fourierChar (-(b * x)) : ℂ)
            * 𝓕⁻ (fun η => φ η * 𝓕 (f : ℝ → ℂ) (η - b)) x :=
            fourierInv_comp_add (fun η => φ η * 𝓕 (f : ℝ → ℂ) (η - b)) b x
      _ = (Real.fourierChar (-(b * x)) : ℂ)
            * 𝓕⁻ (fun η => φ η * 𝓕 ((modSchwartz f b : SchwartzMap ℝ ℂ) : ℝ → ℂ) η) x := by
            rw [hfun₂]
      _ = (Real.fourierChar (-(b * x)) : ℂ)
            * contMulOp φ ((modSchwartz f b : SchwartzMap ℝ ℂ) : ℝ → ℂ) x := rfl
  calc eLpNorm (contMulOp (fun ξ => φ (ξ + b)) (f : ℝ → ℂ)) p volume
      = eLpNorm (contMulOp φ ((modSchwartz f b : SchwartzMap ℝ ℂ) : ℝ → ℂ)) p volume := by
        apply eLpNorm_congr_norm_ae (hf := (contMulOp_continuous_any _ _).aestronglyMeasurable)
          (hg := (contMulOp_continuous_any _ _).aestronglyMeasurable)
        filter_upwards with x
        rw [hpoint x, norm_mul, norm_fourierChar, one_mul]
    _ ≤ ENNReal.ofReal (M : ℝ)
          * eLpNorm ((modSchwartz f b : SchwartzMap ℝ ℂ) : ℝ → ℂ) p volume :=
        h (modSchwartz f b)
    _ = ENNReal.ofReal (M : ℝ) * eLpNorm (f : ℝ → ℂ) p volume := by rw [hgnorm]

end Work.KMTAreas.SupNorm
