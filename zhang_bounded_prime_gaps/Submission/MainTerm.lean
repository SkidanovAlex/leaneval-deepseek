import Mathlib
import Submission.ZetaRatioPole
import Submission.Commons.Analysis.Fourier.fourier_pole_identity

open scoped BigOperators Topology MeasureTheory SchwartzMap FourierTransform
open MeasureTheory

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# The main term of P8 Lemma 4.1: `∫∫ pole⁻¹·f·g = (N/(B·φ(N)))·∫∫ F′G′`

The final step of Polymath8a's Lemma 4.1 evaluates the pole-factor integral
that replaces the kernel.  In the normalization of this project (compare the
`CRITICAL normalization note` in `BOUNDED_GAPS_ROADMAP.md`), the divisor sum's
Fourier expansion in Mathlib's variables carries the kernel factor
`[poleFactor W N (-2πξ) (-2πξ′)]⁻¹`, whose integral against the Fourier
transforms of `A = e^t F(t)` (i.e. `F(t) = e^{-t}A(t)`) is

    (N/(B(x)·φ(N))) · ∫₀^∞ F′(t)G′(t) dt ,      B(x) = (φ(W)/W)·log x ,

by the committed commons Fourier identity `fourier_pole_identity` (L25).
This module records that corollary (`poleFactor_mainTerm`), i.e. the
single-coordinate main term of Lemma 4.1; the `k`-coordinate version is the
`k`-fold product.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- Pointwise rewriting of the inverse pole factor at the rescaled variable
`-2πξ` into the common normalization of `fourier_pole_identity`. -/
lemma poleFactor_inv_eq (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0) {x : ℕ}
    (hlog : Real.log (x : ℝ) ≠ 0) (ξ ξ' : ℝ) :
    (poleFactor W N (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ =
      ((N : ℂ) / (((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ) *
          (N.totient : ℂ))) *
        ((1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ') /
          (2 - 2 * Real.pi * Complex.I * (ξ + ξ'))) := by
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hφW : (W.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW)).ne'
  have hφN : (N.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN)).ne'
  have hlogC : (Real.log (x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
  have h1 : (1 : ℂ) - 2 * Real.pi * Complex.I * ξ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h1' : (1 : ℂ) - 2 * Real.pi * Complex.I * ξ' ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h2 : (2 : ℂ) - 2 * Real.pi * Complex.I * (ξ + ξ') ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hnum1 : (1 : ℂ) + (↑(-(2 * Real.pi * ξ)) : ℂ) * Complex.I =
      1 - 2 * Real.pi * Complex.I * ξ := by push_cast; ring
  have hnum2 : (1 : ℂ) + (↑(-(2 * Real.pi * ξ')) : ℂ) * Complex.I =
      1 - 2 * Real.pi * Complex.I * ξ' := by push_cast; ring
  have hnum3 : (2 : ℂ) + ((↑(-(2 * Real.pi * ξ)) : ℂ) + ↑(-(2 * Real.pi * ξ'))) * Complex.I =
      2 - 2 * Real.pi * Complex.I * (ξ + ξ') := by push_cast; ring
  unfold poleFactor
  rw [hnum1, hnum2, hnum3]
  field_simp [hWc, hNc, hφW, hφN, hlogC, h1, h1', h2]

/-- **The main term of P8 Lemma 4.1, one coordinate.**  For nonzero `W, N` and
Schwartz functions `A, B` (with `F(t) = e^{-t}A(t)`, `G(t) = e^{-t}B(t)`),

    ∫∫ [poleFactor W N (-2πξ) (-2πξ′)]⁻¹ · (𝓕A)(ξ)(𝓕B)(ξ′) dξdξ′
      = (N/(B(x)φ(N))) · ∫₀^∞ F′(t)G′(t) dt . -/
theorem poleFactor_mainTerm (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0) (x : ℕ)
    (hlog : Real.log (x : ℝ) ≠ 0) (A B : SchwartzMap ℝ ℂ) :
    ∫ ξ : ℝ, ∫ ξ' : ℝ,
        (poleFactor W N (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
          (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) A) ξ *
          (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) B) ξ'
      = ((N : ℂ) / (((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ) *
            (N.totient : ℂ))) *
          ∫ t : ℝ in Set.Ioi 0,
            (Complex.exp (-t) * (deriv (⇑A) t - A t)) *
              (Complex.exp (-t) * (deriv (⇑B) t - B t)) := by
  have hpt : ∀ ξ ξ' : ℝ,
      (poleFactor W N (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
          (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) A) ξ *
          (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) B) ξ' =
      ((N : ℂ) / (((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ) *
            (N.totient : ℂ))) *
        (((1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ') /
            (2 - 2 * Real.pi * Complex.I * (ξ + ξ'))) *
          (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) A) ξ *
          (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) B) ξ') := by
    intro ξ ξ'
    rw [poleFactor_inv_eq W N hW hN hlog ξ ξ']
    ring
  calc ∫ ξ : ℝ, ∫ ξ' : ℝ,
        (poleFactor W N (-(2 * Real.pi * ξ)) (-(2 * Real.pi * ξ')) x)⁻¹ *
          (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) A) ξ *
          (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) B) ξ'
      = ∫ ξ : ℝ, ∫ ξ' : ℝ,
          ((N : ℂ) / (((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ) *
              (N.totient : ℂ))) *
            (((1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ') /
                (2 - 2 * Real.pi * Complex.I * (ξ + ξ'))) *
              (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) A) ξ *
              (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) B) ξ') := by
        refine integral_congr_ae ?_
        filter_upwards with ξ
        refine integral_congr_ae ?_
        filter_upwards with ξ'
        exact hpt ξ ξ'
    _ = ((N : ℂ) / (((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ) *
            (N.totient : ℂ))) *
          ∫ ξ : ℝ, ∫ ξ' : ℝ,
            ((1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ') /
                (2 - 2 * Real.pi * Complex.I * (ξ + ξ'))) *
              (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) A) ξ *
              (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) B) ξ' := by
        rw [show (∫ ξ : ℝ, ∫ ξ' : ℝ,
              ((N : ℂ) / (((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ) *
                  (N.totient : ℂ))) *
                (((1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ') /
                    (2 - 2 * Real.pi * Complex.I * (ξ + ξ'))) *
                  (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) A) ξ *
                  (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) B) ξ')) =
            ∫ ξ : ℝ, ((N : ℂ) / (((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ) *
                (N.totient : ℂ))) *
              (∫ ξ' : ℝ,
                ((1 - 2 * Real.pi * Complex.I * ξ) * (1 - 2 * Real.pi * Complex.I * ξ') /
                    (2 - 2 * Real.pi * Complex.I * (ξ + ξ'))) *
                  (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) A) ξ *
                  (SchwartzMap.fourierTransformCLM ℂ (V := ℝ) B) ξ') from by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          exact integral_const_mul _ _]
        rw [integral_const_mul]
    _ = ((N : ℂ) / (((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ) *
            (N.totient : ℂ))) *
          ∫ t : ℝ in Set.Ioi 0,
            (Complex.exp (-t) * (deriv (⇑A) t - A t)) *
              (Complex.exp (-t) * (deriv (⇑B) t - B t)) := by
        rw [Commons.Analysis.Fourier.fourier_pole_identity A B]

end Commons.NumberTheory.MaynardSieve
