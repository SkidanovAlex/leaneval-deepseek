/-
# The wave packet for the `L^p`-multiplier sup-norm bound

This module sets up the test functions used in `Work.KMTAreas.IsLqMultiplierBound_supNorm`: for
`δ > 0` and `x₀ : ℝ` the *wave packet*

`f_δ(x) = δ · e^{2πi x₀ x} · 𝓕⁻η(δ x)`,  `η = kmtEta`,

whose Fourier transform is the rescaled bump `ξ ↦ η((ξ - x₀)/δ)`.  Its properties:

* `wavePacket_apply` — the pointwise formula above;
* (`scaledBump_support`) — the rescaled bump is supported in `[x₀ - δ, x₀ + δ]`.

The pointwise formula is `Work.KMTAreas.SupNorm.fourier_wavePacket_inv`, proved in the sibling
module `fourier_wavePacket_inv.lean`; the forward identity used to rewrite
`contMulOp` is `Work.KMTAreas.SupNorm.fourier_wavePacket_fwd`.
-/
import Mathlib
import Submission.Work.KMTAreas.iw_family
import Submission.Work.KMTAreas.A7.EtaMult
import Submission.Work.KMTAreas.SupNorm.fourier_wavePacket_inv

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped FourierTransform ENNReal NNReal
open MeasureTheory

namespace Work.KMTAreas.SupNorm

open Work.KMTAreas.A7

/-- The rescaled KMT cutoff `ξ ↦ kmtEta ((ξ - x₀)/δ)`. -/
noncomputable def scaledBump (x₀ δ : ℝ) : ℝ → ℂ := fun ξ => Work.KMTContract.kmtEta ((ξ - x₀)/δ)

lemma scaledBump_contDiff (x₀ δ : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (scaledBump x₀ δ) :=
  (etaMult_kmtEta_contDiff).comp (by fun_prop)

lemma scaledBump_apply (x₀ δ ξ : ℝ) :
    scaledBump x₀ δ ξ = Work.KMTContract.kmtEta ((ξ - x₀)/δ) := rfl

lemma scaledBump_support {x₀ δ : ℝ} (hδ : 0 < δ) :
    Function.support (scaledBump x₀ δ) ⊆ Metric.closedBall x₀ δ := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs]
  by_contra h
  rw [not_le] at h
  have h1 : 1 ≤ |(x - x₀)/δ| := by
    rw [abs_div, abs_of_pos hδ, one_le_div hδ]
    exact le_of_lt h
  exact hx (Work.KMTContract.kmtEta_zero h1)

/-- The rescaled cutoff as a Schwartz function. -/
noncomputable def scaledBumpSch (x₀ δ : ℝ) (hδ : 0 < δ) : SchwartzMap ℝ ℂ :=
  HasCompactSupport.toSchwartzMap
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ δ)
      (scaledBump_support hδ))
    (scaledBump_contDiff x₀ δ)

lemma scaledBumpSch_apply {x₀ δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    scaledBumpSch x₀ δ hδ ξ = scaledBump x₀ δ ξ :=
  HasCompactSupport.toSchwartzMap_toFun _ _ ξ

/-- The wave packet `𝓕⁻ (scaled bump)`. -/
noncomputable def wavePacket (x₀ δ : ℝ) (hδ : 0 < δ) : SchwartzMap ℝ ℂ :=
  FourierTransformInv.fourierInv (scaledBumpSch x₀ δ hδ)

lemma wavePacket_fourier {x₀ δ : ℝ} (hδ : 0 < δ) :
    𝓕 (wavePacket x₀ δ hδ) = scaledBumpSch x₀ δ hδ :=
  FourierInvPair.fourier_fourierInv_eq (scaledBumpSch x₀ δ hδ)

lemma wavePacket_fourier_apply {x₀ δ : ℝ} (hδ : 0 < δ) (ξ : ℝ) :
    𝓕 (⇑(wavePacket x₀ δ hδ)) ξ = scaledBump x₀ δ ξ := by
  rw [← SchwartzMap.fourier_coe, wavePacket_fourier, scaledBumpSch_apply]

/-- **Pointwise formula for the wave packet**: `f_δ(x) = δ · e^{2π i x₀ x} · 𝓕⁻η(δx)`. -/
theorem wavePacket_apply {x₀ δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    wavePacket x₀ δ hδ x
      = (δ : ℂ) * (Real.fourierChar (x₀ * x) : ℂ)
          * FourierTransformInv.fourierInv (Work.KMTContract.kmtEta) (δ * x) := by
  have hcoe : wavePacket x₀ δ hδ x
      = FourierTransformInv.fourierInv (fun ξ => Work.KMTContract.kmtEta ((ξ - x₀)/δ)) x := by
    rw [show wavePacket x₀ δ hδ x
        = FourierTransformInv.fourierInv (⇑(scaledBumpSch x₀ δ hδ)) x
        from congrFun (SchwartzMap.fourierInv_coe (scaledBumpSch x₀ δ hδ)) x]
    congr 1
  rw [hcoe, Work.KMTAreas.SupNorm.fourier_wavePacket_inv Work.KMTContract.kmtEta hδ x₀ x]

/-- The Fourier transform of the wave packet is supported in `[x₀ - δ, x₀ + δ]`. -/
lemma wavePacket_fourier_support {x₀ δ : ℝ} (hδ : 0 < δ) :
    Function.support (fun ξ => 𝓕 (⇑(wavePacket x₀ δ hδ)) ξ) ⊆ Metric.closedBall x₀ δ := by
  intro ξ hξ
  simp only [Function.mem_support, ne_eq] at hξ
  rw [wavePacket_fourier_apply] at hξ
  exact scaledBump_support hδ hξ

end Work.KMTAreas.SupNorm
