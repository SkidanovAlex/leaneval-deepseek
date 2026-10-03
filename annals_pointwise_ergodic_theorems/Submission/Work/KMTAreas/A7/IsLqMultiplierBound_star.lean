/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.KMTAreas.isLqMultiplierBound_comp_neg
import Submission.Port.Aesm

/-!
# Conjugating the symbol of a bounded `L^q` Fourier multiplier

The predicate `Work.Analysis.IWMultiplier.IsLqMultiplierBound q φ M` says that the continuous
Fourier multiplier `T_φ = 𝓕⁻ ∘ (φ · 𝓕)` on `ℝ` is bounded on `L^q(ℝ)` with norm at most `M`
(tested on Schwartz functions).  This file proves that the bound is invariant under conjugating the
symbol, `φ ↦ star ∘ φ` (used in the reduction of the *dual-even* exponents of the Ionescu–Wainger
multiplier theorem to the even ones, see `Work.Analysis.IWMultiplier.Gap`).

## The argument

Complex conjugation is *not* a linear operation, but it satisfies two exact identities with the
Fourier transform of `ℝ`:

* `𝓕 (star ∘ F) x = star (𝓕⁻ F x)` for every function `F : ℝ → ℂ` (no integrability needed: if
  `F` is not integrable both sides are `0` in Lean's convention, which is why the proof below can
  go through `integral_conj`, stated without hypotheses);
* equivalently `𝓕 (star ∘ F) y = star (𝓕 F (-y))`.

Combining them with `𝓕⁻ H = 𝓕 (H ∘ (-·))` and `star (star (φ ξ) * 𝓕 F ξ) = φ ξ * star (𝓕 F ξ)`
gives, for *arbitrary* `φ : ℝ → ℂ` and `F : ℝ → ℂ` and every `x`,

  `star (T_{star ∘ φ} F x) = T_{φ ∘ (-·)} (star ∘ F) x`,

i.e. `star ∘ T_{star ∘ φ} = T_{φ ∘ (-·)} ∘ star`.  Since `star` is an isometry of every `L^q`
(`‖star z‖ = ‖z‖`), the `L^q` bound for `T_{star ∘ φ}` follows from the one for `T_{φ ∘ (-·)}`,
which is `Work.KMTAreas.isLqMultiplierBound_comp_neg` (reflection invariance of the multiplier
bound), applied to the Schwartz function `x ↦ star (F x)`.

## Main results

* `Work.KMTAreas.A7.star_fourierInv`, `…fourier_star` — conjugation versus Fourier inversion;
* `Work.KMTAreas.A7.star_contMulOp` — `star ∘ T_{star ∘ φ} = T_{φ ∘ (-·)} ∘ star`;
* `Work.KMTAreas.A7.IsLqMultiplierBound_star` — conjugation invariance of the `L^q` multiplier
  bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped FourierTransform ENNReal NNReal ComplexConjugate Real
open MeasureTheory

namespace Work.KMTAreas.A7

/-! ## Conjugation versus the Fourier transform -/

/-- **Conjugation of the Fourier inversion.**  For an arbitrary function `F : ℝ → ℂ`, conjugating
the inverse Fourier transform is the Fourier transform of the conjugated function.  (Both sides are
`0` when `F` is not integrable, so no hypothesis is needed; `integral_conj` is likewise
unconditional.) -/
theorem star_fourierInv (F : ℝ → ℂ) (x : ℝ) :
    star (𝓕⁻ F x) = 𝓕 (fun ξ : ℝ => star (F ξ)) x := by
  rw [Real.fourierInv_eq', Real.fourier_eq']
  rw [← starRingEnd_apply, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with v
  have h1 : (starRingEnd ℂ) (↑(2 * π * inner ℝ v x) * Complex.I)
      = ↑(-(2 * π * inner ℝ v x)) * Complex.I := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    ring
  simp only [smul_eq_mul]
  rw [map_mul, ← Complex.exp_conj, h1]
  simp only [starRingEnd_apply]
  ring_nf

/-- **Conjugation and the Fourier transform.**  Companion form of `star_fourierInv`: the Fourier
transform of `star ∘ F` at `y` is the conjugate of the Fourier transform of `F` at `-y`. -/
theorem fourier_star (F : ℝ → ℂ) (y : ℝ) :
    𝓕 (fun ξ : ℝ => star (F ξ)) y = star (𝓕 F (-y)) := by
  rw [← Real.fourierInv_eq_fourier_neg (f := F), ← star_fourierInv]

/-! ## The conjugate of a Schwartz function -/

/-- The complex conjugate `x ↦ star (f x)` of a Schwartz function, as a `SchwartzMap`
(postcomposition with the real-linear isometry `Complex.conjCLE`). -/
noncomputable def conjSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) f

@[simp] theorem conjSchwartz_coe (f : SchwartzMap ℝ ℂ) :
    (conjSchwartz f : ℝ → ℂ) = fun x => star (f x) := by
  funext x
  rw [conjSchwartz, SchwartzMap.postcompCLM_apply]
  simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, starRingEnd_apply]

theorem conjSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    conjSchwartz f x = star (f x) :=
  congrFun (conjSchwartz_coe f) x

/-- Conjugation preserves the `L^q` seminorm of a Schwartz function. -/
theorem eLpNorm_conjSchwartz (q : ENNReal) (f : SchwartzMap ℝ ℂ) :
    eLpNorm (conjSchwartz f : ℝ → ℂ) q volume = eLpNorm (f : ℝ → ℂ) q volume := by
  apply eLpNorm_congr_norm_ae (hf := by pw_aesm) (hg := by pw_aesm)
  filter_upwards with x
  rw [conjSchwartz_apply, norm_star]

/-! ## Conjugation of the continuous multiplier -/

/-- **Conjugation of the continuous Fourier multiplier.**  For arbitrary `φ : ℝ → ℂ` and
`F : ℝ → ℂ`, conjugating `T_{star ∘ φ} F` gives the multiplier with symbol `φ ∘ (-·)` applied to
`star ∘ F`: `star ∘ T_{star ∘ φ} = T_{φ ∘ (-·)} ∘ star`. -/
theorem star_contMulOp (φ : ℝ → ℂ) (F : ℝ → ℂ) (x : ℝ) :
    star (Work.Analysis.IWMultiplier.contMulOp (fun ξ : ℝ => star (φ ξ)) F x)
      = Work.Analysis.IWMultiplier.contMulOp (fun ξ : ℝ => φ (-ξ))
          (fun ξ : ℝ => star (F ξ)) x := by
  simp only [Work.Analysis.IWMultiplier.contMulOp]
  rw [star_fourierInv, Real.fourierInv_eq_fourier_comp_neg]
  have hfun : (fun ξ : ℝ => star (star (φ ξ) * 𝓕 F ξ))
      = fun ξ : ℝ => φ (- -ξ) * 𝓕 (fun η : ℝ => star (F η)) (-ξ) := by
    funext ξ
    rw [star_mul, star_star, fourier_star, neg_neg, mul_comm]
  rw [hfun]

/-! ## The `L^q` multiplier bound is conjugation invariant -/

/-- **The `L^q` multiplier bound is invariant under conjugating the symbol.**  If `M` bounds the
operator norm of the Fourier multiplier `T_φ` on `L^q(ℝ)`, then it bounds the operator norm of
`T_{star ∘ φ}`: conjugation is an isometry of `L^q(ℝ)` with `T_{star ∘ φ}` conjugate to
`T_{φ ∘ (-·)}`, and reflection invariance of the bound is
`Work.KMTAreas.isLqMultiplierBound_comp_neg`. -/
theorem IsLqMultiplierBound_star {q : ENNReal} {φ : ℝ → ℂ} {M : NNReal}
    (h : Work.Analysis.IWMultiplier.IsLqMultiplierBound q φ M) :
    Work.Analysis.IWMultiplier.IsLqMultiplierBound q (fun x : ℝ => star (φ x)) M := by
  intro f
  have hneg : Work.Analysis.IWMultiplier.IsLqMultiplierBound q (fun ξ : ℝ => φ (-ξ)) M :=
    Work.KMTAreas.isLqMultiplierBound_comp_neg h
  have hpoint : ∀ x : ℝ, star (Work.Analysis.IWMultiplier.contMulOp (fun ξ : ℝ => star (φ ξ))
        (f : ℝ → ℂ) x)
      = Work.Analysis.IWMultiplier.contMulOp (fun ξ : ℝ => φ (-ξ))
          (conjSchwartz f : ℝ → ℂ) x := by
    intro x
    rw [star_contMulOp]
    simp only [conjSchwartz_coe]
  calc eLpNorm (Work.Analysis.IWMultiplier.contMulOp (fun ξ : ℝ => star (φ ξ))
          (f : ℝ → ℂ)) q volume
      = eLpNorm (fun x : ℝ => star (Work.Analysis.IWMultiplier.contMulOp
          (fun ξ : ℝ => star (φ ξ)) (f : ℝ → ℂ) x)) q volume := by
        exact (eLpNorm_star (f := Work.Analysis.IWMultiplier.contMulOp
          (fun ξ : ℝ => star (φ ξ)) (f : ℝ → ℂ))).symm
    _ = eLpNorm (Work.Analysis.IWMultiplier.contMulOp (fun ξ : ℝ => φ (-ξ))
          (conjSchwartz f : ℝ → ℂ)) q volume := by
        apply eLpNorm_congr_ae
        filter_upwards with x
        exact hpoint x
    _ ≤ ENNReal.ofReal (M : ℝ) * eLpNorm (conjSchwartz f : ℝ → ℂ) q volume :=
        hneg (conjSchwartz f)
    _ = ENNReal.ofReal (M : ℝ) * eLpNorm (f : ℝ → ℂ) q volume := by
        rw [eLpNorm_conjSchwartz]

end Work.KMTAreas.A7
