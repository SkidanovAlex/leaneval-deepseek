/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IWMultiplier.Defs
import Submission.Work.Analysis.CzShift.l2_bound_of_fourier_symbol
import Submission.Port.Aesm

/-!
# The continuous `L²` multiplier bound: `IsLqMultiplierBound 2 φ M` for `‖φ‖ ≤ M`

The predicate `Work.Analysis.IWMultiplier.IsLqMultiplierBound q φ M` bounds the operator norm of the
continuous Fourier multiplier `T_φ f = 𝓕⁻(φ · 𝓕 f)` on `L^q(ℝ)`, tested on Schwartz functions.  This
file proves the case `q = 2`, where the optimal bound is exactly the sup norm `‖φ‖_∞` of the symbol.

The mathematics is Plancherel: `𝓕⁻` is a unitary of `L²(ℝ)`, so for `f` Schwartz
`‖T_φ f‖₂ = ‖φ · 𝓕f‖₂ ≤ ‖φ‖_∞ ‖𝓕f‖₂ = M ‖f‖₂`.

Two points of formalisation need care and are handled here.

* Plancherel is only available in Mathlib for Schwartz functions, whereas the symbol
  `φ · 𝓕f` is an arbitrary bounded (not necessarily smooth, or even measurable) function.
  The companion file `Work.Analysis.CzShift.l2_bound_of_fourier_symbol` supplies Plancherel for
  `L¹ ∩ L²` functions (`Work.Analysis.CzShift.eLpNorm_fourier_eq_of_memLp`), and the inverse
  transform is reduced to the forward one by `𝓕⁻ g = 𝓕 (g ∘ (-·))` together with the invariance of
  the `L^p` seminorm under the measure-preserving reflection `x ↦ -x`.

* No measurability of `φ` is assumed.  If `φ · 𝓕f` is not integrable then `𝓕⁻ (φ · 𝓕f)` vanishes
  pointwise — the Bochner integral of a non-integrable function is `0` — which settles this case.

## Main results

* `Work.Analysis.IWMultiplier.eLpNorm_fourierInv_eq_of_memLp` — Plancherel for the *inverse*
  Fourier transform on `L¹ ∩ L²` functions;
* `Work.Analysis.IWMultiplier.isLqMultiplierBound_two` — the `q = 2` multiplier bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal FourierTransform RealInnerProductSpace
open MeasureTheory

namespace Work.Analysis.IWMultiplier

/-- **Plancherel's theorem for the inverse Fourier transform on `L¹ ∩ L²` functions.**
For an integrable `L²` function `f`, the pointwise inverse Fourier transform `𝓕⁻ f` has the same
`L²` seminorm as `f`.

This is the inverse counterpart of `Work.Analysis.CzShift.eLpNorm_fourier_eq_of_memLp`, obtained by
writing `𝓕⁻ f = 𝓕 (f ∘ (-·))` (`Real.fourierInv_eq_fourier_comp_neg`), applying the forward
Plancherel theorem to `f ∘ (-·)`, and using that the reflection `x ↦ -x` preserves the measure and
hence the `L^p` seminorm. -/
theorem eLpNorm_fourierInv_eq_of_memLp {f : ℝ → ℂ} (hf : Integrable f volume)
    (hf2 : MemLp f 2 volume) :
    eLpNorm (𝓕⁻ f) 2 volume = eLpNorm f 2 volume := by
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have h1 : Integrable (fun x : ℝ => f (-x)) volume := hf.comp_neg
  have h2 : MemLp (fun x : ℝ => f (-x)) 2 volume := hf2.comp_measurePreserving hmp
  calc eLpNorm (𝓕⁻ f) 2 volume = eLpNorm (𝓕 fun x => f (-x)) 2 volume := by
        rw [Real.fourierInv_eq_fourier_comp_neg]
    _ = eLpNorm (fun x => f (-x)) 2 volume :=
        Work.Analysis.CzShift.eLpNorm_fourier_eq_of_memLp h1 h2
    _ = eLpNorm f 2 volume := eLpNorm_comp_measurePreserving hf2.aestronglyMeasurable hmp

/-- **The `q = 2` case of the continuous multiplier bound.**  If the symbol `φ` is bounded by
`M`, then the Fourier multiplier `T_φ = 𝓕⁻ ∘ (φ · 𝓕)` is bounded on `L²(ℝ)` with norm at most `M`:
`IsLqMultiplierBound 2 φ M`.

No measurability of `φ` is required: a non-integrable multiplier `φ · 𝓕f` produces a vanishing
Bochner integral, so the multiplier is then identically zero. -/
theorem isLqMultiplierBound_two {φ : ℝ → ℂ} {M : NNReal} (hM : ∀ x, ‖φ x‖ ≤ (M : ℝ)) :
    IsLqMultiplierBound 2 φ M := by
  intro f
  set F : ℝ → ℂ := ⇑f with hF
  have hFint : Integrable F volume := f.integrable
  have hFmem : MemLp F 2 volume := f.memLp 2 volume
  -- Plancherel for the Schwartz function `F` and its consequence `𝓕F ∈ L²`
  have heLpF : eLpNorm (𝓕 F) 2 volume = eLpNorm F 2 volume :=
    Work.Analysis.CzShift.eLpNorm_fourier_eq_of_memLp hFint hFmem
  have hFmemF : MemLp (𝓕 F) 2 volume :=
    Work.Analysis.CzShift.memLp_fourier_of_memLp hFint hFmem
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
  -- the pointwise bound `‖φ · 𝓕F‖ ≤ ‖M • 𝓕F‖`
  have hpt : ∀ ξ, ‖φ ξ • 𝓕 F ξ‖ ≤ ‖(M : ℂ) • 𝓕 F ξ‖ := by
    intro ξ
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hMnn]
    exact mul_le_mul_of_nonneg_right (hM ξ) (norm_nonneg _)
  have hconst : ‖(M : ℂ)‖ₑ = ENNReal.ofReal (M : ℝ) := by
    rw [← ofReal_norm (M : ℂ), Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hMnn]
  by_cases hInt : Integrable (fun ξ => φ ξ * 𝓕 F ξ) volume
  · -- the multiplier `φ · 𝓕F` is integrable: Plancherel applies
    have hgmem : MemLp (fun ξ => φ ξ * 𝓕 F ξ) 2 volume :=
      MemLp.of_le (hFmemF.const_smul (M : ℂ)) hInt.aestronglyMeasurable
        (by filter_upwards with ξ using hpt ξ)
    have heLpG : eLpNorm (fun ξ => φ ξ * 𝓕 F ξ) 2 volume
        ≤ ENNReal.ofReal (M : ℝ) * eLpNorm (𝓕 F) 2 volume := by
      calc eLpNorm (fun ξ => φ ξ * 𝓕 F ξ) 2 volume
          ≤ eLpNorm (fun ξ => (M : ℂ) • 𝓕 F ξ) 2 volume := eLpNorm_mono (hf := by pw_aesm) (fun ξ => hpt ξ)
        _ = ‖(M : ℂ)‖ₑ * eLpNorm (𝓕 F) 2 volume := by
            rw [show (fun ξ => (M : ℂ) • 𝓕 F ξ) = (M : ℂ) • 𝓕 F from rfl]
            exact eLpNorm_const_smul (M : ℂ) (𝓕 F) 2 volume
        _ = ENNReal.ofReal (M : ℝ) * eLpNorm (𝓕 F) 2 volume := by rw [hconst]
    have hgnegint : Integrable (fun x => (fun ξ => φ ξ * 𝓕 F ξ) (-x)) volume := hInt.comp_neg
    have hgnegmem : MemLp (fun x => (fun ξ => φ ξ * 𝓕 F ξ) (-x)) 2 volume :=
      hgmem.comp_measurePreserving hmp
    have hplan := Work.Analysis.CzShift.eLpNorm_fourier_eq_of_memLp hgnegint hgnegmem
    have hcomp := eLpNorm_comp_measurePreserving (p := 2) hInt.aestronglyMeasurable hmp
    calc eLpNorm (contMulOp φ F) 2 volume
        = eLpNorm (𝓕 (fun x => (fun ξ => φ ξ * 𝓕 F ξ) (-x))) 2 volume := by
          rw [contMulOp, Real.fourierInv_eq_fourier_comp_neg]
      _ = eLpNorm (fun x => (fun ξ => φ ξ * 𝓕 F ξ) (-x)) 2 volume := hplan
      _ = eLpNorm (fun ξ => φ ξ * 𝓕 F ξ) 2 volume := hcomp
      _ ≤ ENNReal.ofReal (M : ℝ) * eLpNorm (𝓕 F) 2 volume := heLpG
      _ = ENNReal.ofReal (M : ℝ) * eLpNorm F 2 volume := by rw [heLpF]
  · -- `φ · 𝓕F` is not integrable: the Bochner integral, hence the multiplier, vanishes
    have hzero : contMulOp φ F = fun _ => 0 := by
      rw [contMulOp, Real.fourierInv_eq_fourier_comp_neg]
      funext x
      rw [Real.fourier_eq]
      refine integral_undef ?_
      rw [Real.fourierIntegral_convergent_iff x]
      intro h
      exact hInt (by simpa [Function.comp_def] using h.comp_neg)
    rw [hzero]
    simp

end Work.Analysis.IWMultiplier
