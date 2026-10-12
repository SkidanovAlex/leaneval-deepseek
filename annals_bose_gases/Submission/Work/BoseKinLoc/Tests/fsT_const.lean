import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Tests.fsT_const` — the constant state carries no kinetic energy

The localised kinetic word `fsT ℓ d s εT b u` of FS `eq:DefT` is a **one-body quadratic
form** built out of the box mean-free projection `Q_u ψ = ψ − |Λ(u)|⁻¹∫_{Λ(u)}ψ`.  On the
constant state `ψ ≡ c` the box mean is `c` (`bsMean_const`, using `|Λ(u)| = ℓ³`), hence
`Q_uψ ≡ 0`, and every one of the four words

* `neuWord` — the Neumann-resolvent fraction `½ε_T(dℓ)⁻²(−Δ^N_u)(−Δ^N_u+(dℓ)⁻²)⁻¹` of
  `Q_uψ` (`neuFrac` is the Dirichlet-principle infimum over smooth compactly supported
  trials; its defining set contains `0` and is bounded below by `0`),
* `gapWord` — the `L²`-mass `bℓ⁻²‖Q_uψ‖²_{Λ(u)}`,
* `momWord` — the large-momentum form, a Fourier form of the zero function,
* `mainWord` — the two-cutoff windowed form `Q_uχ_u{…}χ_uQ_u`, a Fourier form of the zero
  function,

vanishes.  This file proves that from the definitions alone (only `Defs` is imported), so
it doubles as the `N = 1` constant-state test of the chapter's vocabulary: the statement
is *not* vacuous and none of the four pieces degenerates silently — each is separately
shown to be zero, for the reason the physics gives.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Tests

open Submission.BoseGases
open Work.BSKinetic

/-- The box mean of the constant state `c` over `Λ(u) = ℓu + acube ℓ` is `c`
(the box has volume `ℓ³`, `acube_volume`, and `ℓ > 0`). -/
lemma bsMean_const {ℓ c : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) : bsMean ℓ u (fun _ => c) = c := by
  unfold bsMean
  rw [setIntegral_const, Measure.real_def, acube_volume ℓ hℓ.le,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), one_mul]

/-- The mean-free part of the constant state vanishes **everywhere** (not merely on the box). -/
lemma Qfree_const {ℓ c : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    Qfree ℓ u (fun _ => c) = fun _ => (0 : ℝ) := by
  funext z
  simp [Qfree, bsQ, bsMean_const hℓ u]

/-! ## The four words vanish when `Q_uψ` does -/

/-- `neuFrac` of a function that is identically zero is `0`: the defining set of trials is
bounded below by `0` and contains `0` (the trial `g = 0`). -/
lemma neuFrac_eq_zero_of_eq_zero {ℓ a2 : ℝ} (ha2 : 0 ≤ a2) (u : ℝ³) {φ : ℝ³ → ℝ}
    (hφ : ∀ z, φ z = 0) : neuFrac ℓ a2 u φ = 0 := by
  unfold neuFrac
  set S := { c : ℝ | ∃ g : ℝ³ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      c = (∫ z in lamBox ℓ u, (φ z) ^ 2)
          - 2 * a2 * (∫ z in lamBox ℓ u, φ z * g z)
          + a2 * ((∑ k : Fin 3, ∫ z in lamBox ℓ u, (fderiv ℝ g z (kcStdBasis k)) ^ 2)
                  + a2 * (∫ z in lamBox ℓ u, (g z) ^ 2)) } with hS
  have hzero : (0 : ℝ) ∈ S := by
    refine ⟨fun _ : ℝ³ => (0 : ℝ), contDiff_const, HasCompactSupport.zero, ?_⟩
    simp [hφ]
  have hnonneg : ∀ c ∈ S, 0 ≤ c := by
    rintro c ⟨g, -, -, rfl⟩
    simp only [hφ, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, mul_zero, integral_zero,
      sub_zero, zero_add]
    exact mul_nonneg ha2
      (add_nonneg (Finset.sum_nonneg fun k _ => integral_nonneg fun z => sq_nonneg _)
        (mul_nonneg ha2 (integral_nonneg fun z => sq_nonneg _)))
  exact le_antisymm (csInf_le ⟨0, fun c hc => hnonneg c hc⟩ hzero)
    (le_csInf ⟨0, hzero⟩ fun b hb => hnonneg b hb)

/-- The gap mass `gapBare` vanishes. -/
lemma gapBare_eq_zero_of_eq_zero {ℓ : ℝ} (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hQ : ∀ z, Qfree ℓ u ψ z = 0) : gapBare ℓ u ψ = 0 := by
  unfold gapBare
  simp [hQ]

/-- The large-momentum form vanishes: it is a Fourier form of the zero function. -/
lemma momForm_eq_zero_of_eq_zero {ℓ d : ℝ} (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hQ : ∀ z, Qfree ℓ u ψ z = 0) : momForm ℓ d u ψ = 0 := by
  unfold momForm
  have hfun : (fun z : ℝ³ => (((indU ℓ u z : ℝ)) : ℂ) * ((Qfree ℓ u ψ z : ℝ) : ℂ)) = 0 := by
    funext z
    rw [hQ z]
    simp
  rw [hfun]
  simp [kinFT]

/-- The windowed one-body kinetic form vanishes. -/
lemma bsOneBody_eq_zero_of_eq_zero {ℓ : ℝ} (F : ℝ → ℝ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hQ : ∀ z, Qfree ℓ u ψ z = 0) : bsOneBody ℓ F u ψ = 0 := by
  unfold bsOneBody
  have hfun : (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) = 0 := by
    funext z
    have h := hQ z
    simp only [Qfree] at h
    rw [h]
    simp
  rw [hfun]
  simp [kinFT]

/-- **The main vanishing statement**: if `Q_uψ` is identically zero then each of FS
`eq:DefT`'s four words is zero, hence so is `𝒯_uψ = fsT ℓ d s εT b u ψ`. -/
lemma fsT_eq_zero_of_Qfree_eq_zero {ℓ d s εT b : ℝ} (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hQ : ∀ z, Qfree ℓ u ψ z = 0) : fsT ℓ d s εT b u ψ = 0 := by
  have hneu : neuWord ℓ d εT u ψ = 0 := by
    unfold neuWord
    rw [neuFrac_eq_zero_of_eq_zero (by positivity : (0 : ℝ) ≤ (d * ℓ) ^ (-2 : ℤ)) u hQ,
      mul_zero]
  have hgap : gapWord ℓ b u ψ = 0 := by
    unfold gapWord
    rw [gapBare_eq_zero_of_eq_zero u hQ, mul_zero]
  have hmom : momWord ℓ d εT b u ψ = 0 := by
    unfold momWord
    rw [momForm_eq_zero_of_eq_zero u hQ, mul_zero]
  have hmain : mainWord ℓ d s εT u ψ = 0 := by
    unfold mainWord
    rw [bsOneBody_eq_zero_of_eq_zero _ u hQ, bsOneBody_eq_zero_of_eq_zero _ u hQ,
      mul_zero, mul_zero, add_zero]
  rw [fsT_eq_sum, hneu, hgap, hmom, hmain]
  ring

/-! ## The requested lemma -/

theorem fsT_const {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) (c : ℝ) :
    Work.BoseKinLoc.fsT ℓ d s εT b u (fun _ => c) = 0 :=
  fsT_eq_zero_of_Qfree_eq_zero u (fun z => by rw [Qfree_const hℓ u])

end Work.BoseKinLoc.Tests
