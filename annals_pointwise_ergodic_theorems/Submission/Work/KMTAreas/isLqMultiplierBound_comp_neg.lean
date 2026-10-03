import Mathlib
import Submission.Work.Analysis.IWMultiplier.Defs
import Submission.Port.Aesm

/-!
# Reflecting the symbol of the continuous Fourier multiplier

`Work.Analysis.IWMultiplier.IsLqMultiplierBound p φ M` says that the Fourier multiplier
`T_φ = 𝓕⁻ ∘ (φ · 𝓕)` with symbol `φ` is bounded by `M` on `L^p(ℝ)` (tested on Schwartz
functions).  This file shows that the bound is invariant under reflecting the symbol,
`φ ↦ (ξ ↦ φ (-ξ))`.

The proof conjugates `T_{φ(-·)}` by the reflection `R : f ↦ (x ↦ f (-x))`, which is an isometry
of every `L^p(ℝ)` (`eLpNorm_comp_neg`) and preserves the Schwartz space (it is
`SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)`):

* on the Fourier side, reflection is `𝓕 (f ∘ (-·)) = (𝓕 f) ∘ (-·)`, i.e.
  `Real.fourier_comp_linearIsometry` for `A = LinearIsometryEquiv.neg ℝ`;
* hence `T_{φ(-·)} f = R (T_φ (R f))`, and the claim follows from the hypothesis `h` applied to
  the Schwartz function `R f`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTAreas

open scoped FourierTransform ENNReal NNReal
open MeasureTheory

/-- **Reflection invariance of the `L^p` seminorm on `ℝ`.**  Lebesgue measure is invariant under
`x ↦ -x`, hence `eLpNorm` is unchanged by composing (on the right) with the reflection.  The
statement holds for every exponent `p : ℝ≥0∞`, including `p = 0` and `p = ⊤`. -/
theorem eLpNorm_comp_neg (g : ℝ → ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun x => g (-x)) p volume = eLpNorm g p volume := by
  have h := (measurableEmbedding_neg (α := ℝ)).eLpNorm_map_measure (g := g) (μ := volume) (p := p)
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h
  simpa only [Function.comp_def] using h.symm

/-- The reflection `f ↦ (x ↦ f (-x))` of a Schwartz function, as a Schwartz function. -/
noncomputable def negSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  f.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)

@[simp] theorem negSchwartz_coe (f : SchwartzMap ℝ ℂ) :
    (negSchwartz f : ℝ → ℂ) = fun x => f (-x) := by
  rw [negSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rfl

/-- The Fourier transform of the reflection of a Schwartz function is the reflection of its
Fourier transform. -/
theorem fourier_negSchwartz (f : SchwartzMap ℝ ℂ) :
    (𝓕 (negSchwartz f : ℝ → ℂ)) = fun η => 𝓕 (f : ℝ → ℂ) (-η) := by
  rw [negSchwartz_coe]
  funext η
  exact Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) (f : ℝ → ℂ) η

/-- **Conjugation of the continuous multiplier by the reflection.**  The multiplier with symbol
`ξ ↦ φ (-ξ)` is the reflection of the multiplier with symbol `φ` conjugated by the reflection,
`T_{φ(-·)} f = R (T_φ (R f))`. -/
theorem contMulOp_comp_neg (φ : ℝ → ℂ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    Work.Analysis.IWMultiplier.contMulOp (fun ξ : ℝ => φ (-ξ)) (f : ℝ → ℂ) x
      = Work.Analysis.IWMultiplier.contMulOp φ (negSchwartz f : ℝ → ℂ) (-x) := by
  have hFg := fourier_negSchwartz f
  have hA : (fun ξ => φ (-ξ) * 𝓕 (f : ℝ → ℂ) ξ)
      = (fun η => φ η * 𝓕 (negSchwartz f : ℝ → ℂ) η) ∘ (LinearIsometryEquiv.neg ℝ) := by
    funext ξ
    simp only [Function.comp_apply]
    rw [hFg]
    simp
  simp only [Work.Analysis.IWMultiplier.contMulOp]
  rw [hA]
  rw [Real.fourierInv_comp_linearIsometry (LinearIsometryEquiv.neg ℝ)
        (fun η => φ η * 𝓕 (negSchwartz f : ℝ → ℂ) η) x]
  rfl

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

/-- **The `L^p` multiplier bound is invariant under reflecting the symbol.**  If `M` bounds the
operator norm of the Fourier multiplier `T_φ` on `L^p(ℝ)`, then it bounds the operator norm of
`T_{φ(-·)}`: reflection is an isometry of `L^p(ℝ)` conjugating one into the other. -/
theorem isLqMultiplierBound_comp_neg {p : ENNReal} {φ : ℝ → ℂ} {M : NNReal}
    (h : Work.Analysis.IWMultiplier.IsLqMultiplierBound p φ M) :
    Work.Analysis.IWMultiplier.IsLqMultiplierBound p (fun ξ : ℝ => φ (-ξ)) M := by
  intro f
  have hgnorm : eLpNorm (negSchwartz f : ℝ → ℂ) p volume = eLpNorm (f : ℝ → ℂ) p volume := by
    rw [negSchwartz_coe, eLpNorm_comp_neg]
  have hpoint : ∀ x, Work.Analysis.IWMultiplier.contMulOp (fun ξ : ℝ => φ (-ξ))
      (f : ℝ → ℂ) x = Work.Analysis.IWMultiplier.contMulOp φ (negSchwartz f : ℝ → ℂ) (-x) :=
    contMulOp_comp_neg φ f
  calc eLpNorm (Work.Analysis.IWMultiplier.contMulOp (fun ξ : ℝ => φ (-ξ)) (f : ℝ → ℂ))
        p volume
      = eLpNorm (fun x => Work.Analysis.IWMultiplier.contMulOp φ (negSchwartz f : ℝ → ℂ) (-x))
          p volume := by
        apply eLpNorm_congr_norm_ae (hf := (contMulOp_continuous_any _ _).aestronglyMeasurable)
          (hg := (((contMulOp_continuous_any _ _).comp continuous_neg).aestronglyMeasurable :
            AEStronglyMeasurable (fun x => Work.Analysis.IWMultiplier.contMulOp φ
              (negSchwartz f : ℝ → ℂ) (-x)) volume))
        filter_upwards with x
        rw [hpoint x]
        rfl
    _ = eLpNorm (Work.Analysis.IWMultiplier.contMulOp φ (negSchwartz f : ℝ → ℂ)) p volume :=
        eLpNorm_comp_neg _ p
    _ ≤ ENNReal.ofReal (M : ℝ) * eLpNorm (negSchwartz f : ℝ → ℂ) p volume := h (negSchwartz f)
    _ = ENNReal.ofReal (M : ℝ) * eLpNorm (f : ℝ → ℂ) p volume := by rw [hgnorm]

end Work.KMTAreas
