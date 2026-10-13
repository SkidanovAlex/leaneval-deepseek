/-
Copyright: work module for the Elgindi finite-time singularity project.

# Plancherel for the `t`-Fourier slice, first order, with a derivative

`Work.FTS.EllSol.FlatFT.plancherelSlice1Deriv`:
`∫ ξ, (2πξ)² ‖slice1 h ξ‖² = ∫ t, ‖deriv h t‖²` for `h : ℝ → ℂ` of class `C¹` with compact
support.

The pointwise derivative rule for the Fourier transform (Mathlib's `Real.fourier_deriv`)
`𝓕 (deriv h) ξ = 2πIξ · 𝓕 h ξ` identifies `slice1 (deriv h)` with `2πIξ · slice1 h`; taking
norms and squaring turns the weight `(2πξ)²` into the modulus squared of that factor, so the
statement reduces to Plancherel for the compactly supported continuous function `deriv h`
(the sibling `Work.FTS.EllSol.FlatFT.plancherelSlice1`).
-/
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped FourierTransform

namespace Work.FTS.EllSol.FlatFT

noncomputable section

/-- The modulus squared of the factor `2πIξ` acting on `ℂ`. -/
theorem norm_sq_mul_two_pi_I (F : ℂ) (ξ : ℝ) :
    ‖(2 * Real.pi * Complex.I * ξ) * F‖ ^ 2 = (2 * Real.pi * ξ) ^ 2 * ‖F‖ ^ 2 := by
  have h1 : ((2 * Real.pi * Complex.I * ξ : ℂ)) = ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1, norm_mul, norm_mul, Complex.norm_I, mul_one, mul_pow, Complex.sq_norm,
    Complex.normSq_ofReal]
  ring

/-- The pointwise derivative rule for the `t`-slice: `slice1 (deriv h) ξ = 2πIξ · slice1 h ξ`. -/
theorem slice1_deriv (h : ℝ → ℂ) (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (ξ : ℝ) :
    slice1 (deriv h) ξ = (2 * Real.pi * Complex.I * ξ) * slice1 h ξ := by
  rw [slice1_eq_fourier, slice1_eq_fourier]
  have hint : Integrable h := hh.continuous.integrable_of_hasCompactSupport hs
  have h'cont : Continuous (deriv h) := hh.continuous_deriv_one
  have h'supp : HasCompactSupport (deriv h) := hs.deriv
  have h'int : Integrable (deriv h) := h'cont.integrable_of_hasCompactSupport h'supp
  have hfd := Real.fourier_deriv hint (hh.differentiable (by norm_num)) h'int
  rw [congr_fun hfd ξ, smul_eq_mul]

theorem plancherelSlice1Deriv (h : ℝ → ℂ) (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) :
    ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖Work.FTS.EllSol.FlatFT.slice1 h ξ‖ ^ 2
      = ∫ t : ℝ, ‖deriv h t‖ ^ 2 := by
  have h'cont : Continuous (deriv h) := hh.continuous_deriv_one
  have h'supp : HasCompactSupport (deriv h) := hs.deriv
  calc ∫ ξ : ℝ, (2 * Real.pi * ξ) ^ 2 * ‖slice1 h ξ‖ ^ 2
      = ∫ ξ : ℝ, ‖slice1 (deriv h) ξ‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with ξ
        rw [slice1_deriv h hh hs ξ, norm_sq_mul_two_pi_I]
    _ = ∫ t : ℝ, ‖deriv h t‖ ^ 2 := plancherelSlice1 (deriv h) h'cont h'supp

end

end Work.FTS.EllSol.FlatFT
