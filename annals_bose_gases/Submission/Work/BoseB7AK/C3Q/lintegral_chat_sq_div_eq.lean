import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseB7AK.W1rows.W1omega0_rows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.C3Q.lintegral_chat_sq_div_eq` — the Fourier form of the Newtonian
(Coulomb) energy in the `p`-convention

For a real, **even**, nonnegative integrable kernel `W` on `ℝ³` this module proves

  `∫⁻ p, ofReal (Ŵ(p)² / ‖p‖²) = ofReal (2 π²) · ∫⁻ x, ∫⁻ y, ofReal (W x · W y / ‖x − y‖)`,

where `Ŵ = Work.BoseFixR.chat W` is the `p`-convention Fourier transform
`Ŵ(p) = ∫ e^{−i⟨p,y⟩} W(y) dy` (`kinFT_eq_fourier`: `Ŵ(p) = Re 𝓕W((2π)⁻¹ • p)`).

This is the classical identity `∫ |Ŵ(p)|²/|p|² dp = 2π² ∬ W(x)W(y)/|x−y| dx dy`
(the Hardy–Littlewood–Sobolev / Newtonian-energy identity for the Coulomb kernel
`1/|x|`), stated in `ℝ≥0∞` so that it covers the case where **both** sides are `∞`.
Only `W ∈ L¹` is needed, together with the parity `W(−x) = W(x)` — the latter is
exactly what makes the real part `chat` carry the full modulus of the Fourier
transform (`𝓕W` is real-valued for even real `W`).

## Route

* `chat_sq_eq_fourier_normSq` : `Ŵ(p)² = ‖𝓕W((2π)⁻¹ • p)‖²` pointwise.  By
  `kinFT_eq_fourier`, `Ŵ(p)` is the real part of `𝓕W((2π)⁻¹ • p)`; the imaginary
  part is `−∫ sin(2π⟨x,q⟩) W(x) dx`, whose integrand is *odd* when `W` is even, so
  it vanishes (`MeasureTheory.integral_neg_eq_self` plus `integral_neg`).
* `lintegral_fourier_inv_smul_normSq_div_eq` : the Coulomb identity
  `Commons.Analysis.Fourier.coulomb_energy_fourier_lintegral_eq`
  (`∫⁻ ‖𝓕f(q)‖²/‖q‖² dq = ofReal π · ∬ f f /‖x−y‖` for `0 ≤ f` integrable) in the
  `p`-convention, obtained by the substitution `p = (2π) q`
  (`Commons.Analysis.Fourier.lintegral_comp_inv_smul_of_pos`); the two `(2π)`-powers
  combine into the factor `2π²`.
* `lintegral_chat_sq_div_eq` : combine the two pointwise, via `lintegral_congr`.
-/

set_option maxHeartbeats 1000000

open MeasureTheory
open scoped Real FourierTransform ENNReal

namespace Work.BoseB7AK.C3Q

noncomputable section

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- **`Ŵ(p)² = ‖𝓕W((2π)⁻¹ • p)‖²`.**  For an *even* real function `W`, Mathlib's
complex Fourier transform of `W` is real-valued, so the real part `Work.BoseFixR.chat`
already carries the full modulus.  No integrability of `W` is needed: for a
non-integrable function Mathlib's integral is `0`, for which the claim is trivial. -/
theorem chat_sq_eq_fourier_normSq {W : R3 → ℝ}
    (hWe : ∀ x, W (-x) = W x)
    (p : R3) :
    (Work.BoseFixR.chat W p) ^ 2
      = ‖(FourierTransform.fourier (fun x => (W x : ℂ)) : R3 → ℂ)
          ((2 * Real.pi)⁻¹ • p)‖ ^ 2 := by
  have hchat : Work.BoseFixR.chat W p
      = (FourierTransform.fourier (fun x => (W x : ℂ)) ((2 * Real.pi)⁻¹ • p)).re := by
    rw [Work.BoseFixR.chat]
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  -- the Fourier transform of an even real function is real
  have him : ∀ q : R3, (FourierTransform.fourier (fun x => (W x : ℂ)) q).im = 0 := by
    intro q
    rw [Real.fourier_eq']
    set u : R3 → ℂ :=
      fun x => Complex.exp (↑(-2 * Real.pi * inner ℝ x q) * Complex.I) • (W x : ℂ) with hu
    -- the sine-integral vanishes by oddness
    have hzero : (∫ x : R3, Real.sin (2 * Real.pi * inner ℝ x q) * W x) = 0 := by
      set g : R3 → ℝ := fun x => Real.sin (2 * Real.pi * inner ℝ x q) * W x with hg
      have hgn : (fun x : R3 => g (-x)) = fun x => -g x := by
        funext x
        simp only [hg, inner_neg_left, mul_neg, Real.sin_neg, neg_mul, hWe x]
      have h1 : (∫ x : R3, g (-x)) = ∫ x : R3, g x :=
        MeasureTheory.integral_neg_eq_self g volume
      rw [hgn, MeasureTheory.integral_neg] at h1
      linarith
    have himu : ∀ x : R3, (u x).im = -(Real.sin (2 * Real.pi * inner ℝ x q) * W x) := by
      intro x
      have harg : -2 * Real.pi * inner ℝ x q = -(2 * Real.pi * inner ℝ x q) := by ring
      have hsin : Real.sin (-2 * Real.pi * inner ℝ x q)
          = -Real.sin (2 * Real.pi * inner ℝ x q) := by
        rw [harg, Real.sin_neg]
      have hexp : Complex.exp (↑(-2 * Real.pi * inner ℝ x q) * Complex.I)
          = ⟨Real.cos (-2 * Real.pi * inner ℝ x q),
             Real.sin (-2 * Real.pi * inner ℝ x q)⟩ := by
        apply Complex.ext
        · rw [Complex.exp_ofReal_mul_I_re]
        · rw [Complex.exp_ofReal_mul_I_im]
      simp only [hu, hexp, smul_eq_mul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, zero_add, hsin]
      ring
    by_cases hInt : Integrable u
    · have h3 : (∫ x : R3, u x).im = ∫ x : R3, (u x).im := by
        have hh := Complex.imCLM.integral_comp_comm (φ := u) hInt
        simpa using hh.symm
      have h4 : (∫ x : R3, (u x).im) = 0 := by
        simp only [himu]
        rw [MeasureTheory.integral_neg, hzero, neg_zero]
      rw [h3, h4]
    · rw [MeasureTheory.integral_undef hInt]
      simp
  rw [hchat]
  have hns : Complex.normSq (FourierTransform.fourier (fun x => (W x : ℂ))
      ((2 * Real.pi)⁻¹ • p))
      = (FourierTransform.fourier (fun x => (W x : ℂ)) ((2 * Real.pi)⁻¹ • p)).re ^ 2 := by
    rw [Complex.normSq_apply, him]
    ring
  rw [Complex.normSq_eq_norm_sq] at hns
  rw [hns]

/-- **The Coulomb-energy identity in the `p`-convention.**  This is
`Commons.Analysis.Fourier.coulomb_energy_fourier_lintegral_eq`
(`∫⁻ ‖𝓕f(q)‖²/‖q‖² dq = ofReal π · ∫⁻x ∫⁻y ofReal (f x · f y/‖x−y‖)`) pushed through
the substitution `p = (2π) q` (`lintegral_comp_inv_smul_of_pos`); the constants
combine to `ofReal (2π) · ofReal π = ofReal (2 π²)`. -/
theorem lintegral_fourier_inv_smul_normSq_div_eq {f : R3 → ℝ}
    (hf : MeasureTheory.Integrable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫⁻ p, ENNReal.ofReal (‖(FourierTransform.fourier (fun x => (f x : ℂ))
        : R3 → ℂ) ((2 * Real.pi)⁻¹ • p)‖ ^ 2 / ‖p‖ ^ 2)
      = ENNReal.ofReal (2 * Real.pi ^ 2) *
          ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * f y / ‖x - y‖) := by
  set c : ℝ := 2 * Real.pi with hcdef
  have hc : 0 < c := by rw [hcdef]; positivity
  have hcne : c ≠ 0 := ne_of_gt hc
  set Fh : R3 → ℂ := FourierTransform.fourier (fun x => (f x : ℂ)) with hFhdef
  set Y : ℝ≥0∞ := ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * f y / ‖x - y‖) with hYdef
  set Z : ℝ≥0∞ := ∫⁻ p, ENNReal.ofReal (‖Fh p‖ ^ 2 / ‖p‖ ^ 2) with hZdef
  have hZ : Z = ENNReal.ofReal Real.pi * Y := by
    rw [hZdef, hYdef, hFhdef]
    exact Commons.Analysis.Fourier.coulomb_energy_fourier_lintegral_eq hf hf0
  -- rescale the `‖p‖⁻²` factor to `‖c⁻¹ • p‖⁻²`
  have hpt : ∀ p : R3, ENNReal.ofReal (‖Fh (c⁻¹ • p)‖ ^ 2 / ‖p‖ ^ 2)
      = ENNReal.ofReal ((c⁻¹) ^ 2) *
          ENNReal.ofReal (‖Fh (c⁻¹ • p)‖ ^ 2 / ‖c⁻¹ • p‖ ^ 2) := by
    intro p
    by_cases hp : p = 0
    · subst hp
      simp
    · have hnorm : ‖c⁻¹ • p‖ ^ 2 = (c⁻¹) ^ 2 * ‖p‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hc.le)]
        ring
      have hb : ‖p‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hp)
      have hc2 : (c⁻¹) ^ 2 ≠ 0 := pow_ne_zero _ (inv_ne_zero hcne)
      rw [hnorm, ← ENNReal.ofReal_mul (sq_nonneg (c⁻¹))]
      congr 1
      field_simp
  have h1 : (∫⁻ p, ENNReal.ofReal (‖Fh (c⁻¹ • p)‖ ^ 2 / ‖p‖ ^ 2))
      = ENNReal.ofReal ((c⁻¹) ^ 2) *
          ∫⁻ p, ENNReal.ofReal (‖Fh (c⁻¹ • p)‖ ^ 2 / ‖c⁻¹ • p‖ ^ 2) := by
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- change of variables `p = c q`
  have h2 : (∫⁻ p, ENNReal.ofReal (‖Fh (c⁻¹ • p)‖ ^ 2 / ‖c⁻¹ • p‖ ^ 2))
      = ENNReal.ofReal (c ^ 3) * Z := by
    have hsc := Commons.Analysis.Fourier.lintegral_comp_inv_smul_of_pos
      (volume : Measure R3) (fun p : R3 => ENNReal.ofReal (‖Fh p‖ ^ 2 / ‖p‖ ^ 2)) hc
    simp only [finrank_euclideanSpace, Fintype.card_fin] at hsc
    rw [hsc, ← hZdef]
  have hconst : ENNReal.ofReal ((c⁻¹) ^ 2) * ENNReal.ofReal (c ^ 3)
      * ENNReal.ofReal Real.pi = ENNReal.ofReal (2 * Real.pi ^ 2) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg (c⁻¹)), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hcdef]
    field_simp
  have key : (∫⁻ p, ENNReal.ofReal (‖Fh (c⁻¹ • p)‖ ^ 2 / ‖p‖ ^ 2))
      = ENNReal.ofReal (2 * Real.pi ^ 2) * Y := by
    rw [h1, h2, hZ]
    calc ENNReal.ofReal ((c⁻¹) ^ 2) *
            (ENNReal.ofReal (c ^ 3) * (ENNReal.ofReal Real.pi * Y))
        = (ENNReal.ofReal ((c⁻¹) ^ 2) * ENNReal.ofReal (c ^ 3)
            * ENNReal.ofReal Real.pi) * Y := by ring
      _ = ENNReal.ofReal (2 * Real.pi ^ 2) * Y := by rw [hconst]
  simpa only [hFhdef, hcdef, hYdef] using key

/-- **The Fourier form of the Newtonian (Coulomb) energy in the `p`-convention.**
For an even, nonnegative integrable kernel `W`,

  `∫⁻ p, ofReal (Ŵ(p)²/‖p‖²) = ofReal (2 π²) · ∫⁻ x, ∫⁻ y, ofReal (W x · W y/‖x−y‖)`,

where `Ŵ = Work.BoseFixR.chat W`. -/
theorem lintegral_chat_sq_div_eq {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hW0 : ∀ x, 0 ≤ W x) (hWe : ∀ x, W (-x) = W x) :
    ∫⁻ p, ENNReal.ofReal ((Work.BoseFixR.chat W p) ^ 2 / ‖p‖ ^ 2)
      = ENNReal.ofReal (2 * Real.pi ^ 2) *
          ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖) := by
  calc ∫⁻ p, ENNReal.ofReal ((Work.BoseFixR.chat W p) ^ 2 / ‖p‖ ^ 2)
      = ∫⁻ p, ENNReal.ofReal (‖(FourierTransform.fourier (fun x => (W x : ℂ))
            : EuclideanSpace ℝ (Fin 3) → ℂ) ((2 * Real.pi)⁻¹ • p)‖ ^ 2 / ‖p‖ ^ 2) := by
        apply lintegral_congr
        intro p
        rw [chat_sq_eq_fourier_normSq hWe p]
    _ = ENNReal.ofReal (2 * Real.pi ^ 2) *
          ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖) :=
        lintegral_fourier_inv_smul_normSq_div_eq hW hW0

end

end Work.BoseB7AK.C3Q
