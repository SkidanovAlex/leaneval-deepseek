/-
# Elementary preparations for the per-arc shift-difference bound

This module collects the small, self-contained facts used by the proof of
`Work.KMTAreas.A7.varShiftDiffSingleArc`:

* `iwArithFreqs_zero` — the exact-height-`0` arithmetic frequency set is `{0}`, so that the
  Ionescu--Wainger projection `Tle ρ 0` is the plain convolution with the kernel of the
  periodised symbol (`Tle_zero_eq`);
* `periodize_mul_of_narrow` — the periodisation of a product of two narrow functions is the
  product of the periodisations;
* `summable_fourierCoeff_periodize` — the Fourier coefficients of the periodisation of a
  compactly supported `C²` function are summable (indeed absolutely summable, with quadratic
  decay);
* the elementary support/plateau facts for the rescaled cutoff `x ↦ cutBump (x/β)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.tsum_norm_iwKernel_le
import Submission.Work.KMTAreas.A7.liftCollapse

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

open Work.Analysis.IonescuWainger

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## The arithmetic frequency set of exact height `0` -/

theorem iwArithFreqs_zero (ρ : ℝ) : iwArithFreqs ρ 0 = ({0} : Finset Circ) := by
  unfold iwArithFreqs iwP
  simp

theorem iwSymbolSet_zero_left (Ψ : Circ → ℂ) :
    iwSymbolSet ({0} : Finset Circ) Ψ = Ψ := by
  funext ξ
  simp [iwSymbolSet]

/-- **`Tle ρ 0` is the plain convolution with the kernel of the periodised symbol.** -/
theorem Tle_zero_eq (ρ : ℝ) (φ : ℝ → ℂ) (f : ℤ → ℂ) :
    Tle ρ 0 φ f = fun x : ℤ => ∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel (periodize φ) j * f (x - j) := by
  funext x
  rw [Tle_apply]
  refine tsum_congr (fun j => ?_)
  rw [iwArithFreqs_zero ρ, iwSymbolSet_zero_left]

/-! ## Multiplicativity of the periodisation over narrow supports -/

/-- **The periodisation of a product of narrow functions is the product of the
periodisations.**  Both factors must be supported in `[-w,w]` with `w < 1/2`, so that the
periodisation collapses to the evaluation at the canonical lift (`periodize_eq_lift`). -/
theorem periodize_mul_of_narrow {φ ψ : ℝ → ℂ} {w : ℝ} (hw : w < 1/2)
    (hφ : ∀ x : ℝ, φ x ≠ 0 → |x| ≤ w) (hψ : ∀ x : ℝ, ψ x ≠ 0 → |x| ≤ w) :
    periodize (fun x : ℝ => φ x * ψ x)
      = fun γ : Circ => periodize φ γ * periodize ψ γ := by
  funext γ
  rw [periodize_mul_eq_lift hw hφ γ, periodize_eq_lift hw hφ γ, periodize_eq_lift hw hψ γ]

/-! ## Summability of the Fourier coefficients of the periodisation of a bump -/

/-- **The Fourier coefficients of the periodisation of a compactly supported `C²` function are
absolutely summable**, with the quadratic decay of `iwKernel_decay_of_bump`. -/
theorem summable_norm_fourierCoeff_periodize {F : ℝ → ℂ} (hFcd : ContDiff ℝ 2 F)
    (hFcs : HasCompactSupport F) :
    Summable (fun j : ℤ => ‖fourierCoeff (periodize F) j‖) := by
  set S : ℝ := max (∫ y, ‖F y‖) (∫ y, ‖iteratedDeriv 2 F y‖) with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact le_trans (integral_nonneg fun y => norm_nonneg _) (le_max_left _ _)
  have h1 : (∫ y, ‖F y‖) ≤ S := by rw [hS]; exact le_max_left _ _
  have h2 : (∫ y, ‖iteratedDeriv 2 F y‖) ≤ S := by rw [hS]; exact le_max_right _ _
  have hdec := iwKernel_decay_of_bump ({0} : Finset Circ) hFcd hFcs hSnn h1 h2
  have hbound : ∀ j : ℤ, ‖fourierCoeff (periodize F) j‖
      ≤ (4 * ((({0} : Finset Circ).card : ℝ) * S) + 1) * ‖kmtKernWeight j‖ := by
    intro j
    have h := hdec j
    rwa [iwSymbolSet_zero_left, Work.Analysis.IWMultiplier.iwKernel] at h
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _) hbound
    (summable_kmtKernWeight.mul_left (4 * ((({0} : Finset Circ).card : ℝ) * S) + 1))

/-! ## The rescaled cutoff -/

end

end Work.KMTAreas.A7

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

open Work.Analysis.IonescuWainger

/-- The Fourier coefficients of the periodisation of a bump are summable (non-norm form). -/
theorem summable_fourierCoeff_periodize {F : ℝ → ℂ} (hFcd : ContDiff ℝ 2 F)
    (hFcs : HasCompactSupport F) :
    Summable (fun j : ℤ => fourierCoeff (periodize F) j) :=
  (summable_norm_fourierCoeff_periodize hFcd hFcs).of_norm

end

end Work.KMTAreas.A7
