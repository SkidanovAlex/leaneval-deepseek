import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.low_freq_defs
import Submission.Work.GM.Affine.weighted_plancherel_of_char
import Submission.Work.GM.Affine.integral_tri_div_fourierChar

/-!
# Weighted Plancherel with the squared-sinc weight

For `Y > 0` and `f : ℝ → ℝ` continuous with compact support,

`∫ ξ, sinc (π (ξ / Y))^2 * ‖Fhat f ξ‖^2 = ∫ z, f z * ∫ u, Y * tri (Y (z - u)) f u`.

This is the Plancherel identity for the weight `θ ξ = sinc (π ξ/Y)^2`, whose inverse Fourier
transform is `K x = Y * tri (Y x)` (the Fourier pair `∫ sinc (π y)^2 e(s y) dy = tri s`
rescaled). The main tool is `weighted_plancherel_of_char` of
`Submission.Work.GM.Affine.weighted_plancherel_of_char`.
-/

open MeasureTheory
open scoped FourierTransform

namespace Work.GM.Affine

noncomputable section

/-- Fourier pair for the squared sinc function: for `Y > 0`,
`∫ ξ, sinc (π (ξ / Y))^2 * e(s ξ) dξ = Y * tri (Y s)`, where `e(t) = e^{2π i t}`.
This is the rescaling `ξ = Y y` of `∫ y, sinc (π y)^2 e^{-2π i y (sY)} dy = tri (sY)`
together with the evenness of the squared sinc function. -/
theorem char_identity_sinc_sq {Y : ℝ} (hY : 0 < Y) (s : ℝ) :
    ∫ ξ : ℝ, ((Real.sinc (Real.pi * (ξ / Y)) ^ 2 : ℝ) : ℂ) * (Real.fourierChar (s * ξ) : ℂ)
      = ((Y * Commons.Analysis.Fourier.tri (Y * s) : ℝ) : ℂ) := by
  set G : ℝ → ℂ := fun y => ((Real.sinc (Real.pi * y) ^ 2 : ℝ) : ℂ)
      * Complex.exp (↑(2 * Real.pi * (s * Y) * y) * Complex.I) with hG
  -- the integrand is `G (ξ / Y)`
  have hpt : ∀ ξ : ℝ,
      ((Real.sinc (Real.pi * (ξ / Y)) ^ 2 : ℝ) : ℂ) * (Real.fourierChar (s * ξ) : ℂ)
        = G (ξ / Y) := by
    intro ξ
    rw [Real.fourierChar_apply, hG]
    congr 1
    rw [show 2 * Real.pi * (s * ξ) = 2 * Real.pi * (s * Y) * (ξ / Y) by field_simp]
  -- the Fourier pair with the `+` sign in the exponential
  have hGint : ∫ y : ℝ, G y = ((Commons.Analysis.Fourier.tri (s * Y) : ℝ) : ℂ) := by
    have hC := Commons.Analysis.Fourier.integral_sinc_pi_sq_mul_exp (s * Y)
    have hconj : (starRingEnd ℂ)
        (∫ y : ℝ, ((Real.sinc (Real.pi * y) ^ 2 : ℝ) : ℂ)
          * Complex.exp (↑(-(2 * Real.pi * y * (s * Y))) * Complex.I)) = ∫ y : ℝ, G y := by
      rw [← integral_conj]
      apply integral_congr_ae
      filter_upwards with y
      simp only [hG]
      rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring_nf
    rw [hC] at hconj
    exact hconj.symm.trans (Complex.conj_ofReal _)
  calc ∫ ξ : ℝ, ((Real.sinc (Real.pi * (ξ / Y)) ^ 2 : ℝ) : ℂ) * (Real.fourierChar (s * ξ) : ℂ)
      = ∫ ξ : ℝ, G (ξ / Y) := integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = |Y| • ∫ y : ℝ, G y := MeasureTheory.Measure.integral_comp_div G Y
    _ = Y • ∫ y : ℝ, G y := by rw [abs_of_pos hY]
    _ = Y • ((Commons.Analysis.Fourier.tri (s * Y) : ℝ) : ℂ) := by rw [hGint]
    _ = ((Y * Commons.Analysis.Fourier.tri (Y * s) : ℝ) : ℂ) := by
        rw [Complex.real_smul]
        rw [show (Y : ℂ) * ((Commons.Analysis.Fourier.tri (s * Y) : ℝ) : ℂ)
              = ((Y * Commons.Analysis.Fourier.tri (Y * s) : ℝ) : ℂ) from by
          rw [← Complex.ofReal_mul, show Y * Commons.Analysis.Fourier.tri (s * Y)
              = Y * Commons.Analysis.Fourier.tri (Y * s) from by rw [mul_comm s Y]]]

theorem weighted_plancherel_sinc_sq {Y : ℝ} (hY : 0 < Y) {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    ∫ ξ : ℝ, (Real.sinc (Real.pi * (ξ / Y))) ^ 2 * ‖Work.GM.Affine.Fhat f ξ‖ ^ 2
      = ∫ z : ℝ, f z * ∫ u : ℝ, Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u := by
  -- integrability of the weight
  have hθint : Integrable (fun ξ : ℝ => Real.sinc (Real.pi * (ξ / Y)) ^ 2) := by
    have h := Commons.Analysis.Fourier.integrable_sinc_pi_sq.comp_mul_left' (R := 1 / Y)
      (by positivity)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  -- boundedness of the weight
  have hθbdd : ∃ M : ℝ, ∀ ξ : ℝ, ‖Real.sinc (Real.pi * (ξ / Y)) ^ 2‖ ≤ M := by
    refine ⟨1, fun ξ => ?_⟩
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (Real.abs_sinc_le_one _)
  -- the Fourier pair defining the kernel
  have hchar : ∀ s : ℝ, ∫ ξ : ℝ, ((Real.sinc (Real.pi * (ξ / Y)) ^ 2 : ℝ) : ℂ)
        * (Real.fourierChar (s * ξ) : ℂ)
      = ((Y * Commons.Analysis.Fourier.tri (Y * s) : ℝ) : ℂ) :=
    fun s => char_identity_sinc_sq hY s
  have hg : Continuous (fun u : ℝ => ((f u : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hf
  have hcs' : HasCompactSupport (fun u : ℝ => ((f u : ℝ) : ℂ)) := by
    simpa [Function.comp_def] using hcs.comp_left (g := fun z : ℝ => ((z : ℝ) : ℂ)) (by simp)
  -- the complex form of weighted Plancherel
  have hmain := weighted_plancherel_of_char (g := fun u : ℝ => ((f u : ℝ) : ℂ)) hg hcs'
    (θ := fun ξ : ℝ => Real.sinc (Real.pi * (ξ / Y)) ^ 2)
    (K := fun x : ℝ => Y * Commons.Analysis.Fourier.tri (Y * x)) hθint hθbdd hchar
  have hmain' : (∫ ξ : ℝ, ((Real.sinc (Real.pi * (ξ / Y)) ^ 2
        * ‖FourierTransform.fourier (fun u : ℝ => ((f u : ℝ) : ℂ)) ξ‖ ^ 2 : ℝ) : ℂ))
      = ∫ z : ℝ, star ((f z : ℝ) : ℂ)
          * ∫ u : ℝ, ((Y * Commons.Analysis.Fourier.tri (Y * (z - u)) : ℝ) : ℂ)
              * ((f u : ℝ) : ℂ) := hmain
  apply Complex.ofReal_inj.mp
  rw [show ((∫ ξ : ℝ, Real.sinc (Real.pi * (ξ / Y)) ^ 2 * ‖Fhat f ξ‖ ^ 2 : ℝ) : ℂ)
      = ∫ ξ : ℝ, ((Real.sinc (Real.pi * (ξ / Y)) ^ 2 * ‖Fhat f ξ‖ ^ 2 : ℝ) : ℂ) from
    (integral_ofReal (f := fun ξ : ℝ => Real.sinc (Real.pi * (ξ / Y)) ^ 2 * ‖Fhat f ξ‖ ^ 2)).symm]
  simp only [Fhat]
  rw [hmain']
  rw [show ((∫ z : ℝ, f z * ∫ u : ℝ, Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u : ℝ) : ℂ)
      = ∫ z : ℝ, ((f z * ∫ u : ℝ, Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u : ℝ) : ℂ) from
    (integral_ofReal (f := fun z : ℝ =>
      f z * ∫ u : ℝ, Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u)).symm]
  apply integral_congr_ae
  filter_upwards with z
  -- the inner integral is real
  rw [show (∫ u : ℝ, ((Y * Commons.Analysis.Fourier.tri (Y * (z - u)) : ℝ) : ℂ) * ((f u : ℝ) : ℂ))
      = ((∫ u : ℝ, Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u : ℝ) : ℂ) from by
    rw [show ((∫ u : ℝ, Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u : ℝ) : ℂ)
        = ∫ u : ℝ, ((Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u : ℝ) : ℂ) from
      (integral_ofReal (f := fun u : ℝ =>
        Y * Commons.Analysis.Fourier.tri (Y * (z - u)) * f u)).symm]
    apply integral_congr_ae
    filter_upwards with u
    exact (Complex.ofReal_mul _ _).symm]
  rw [RCLike.star_def, Complex.conj_ofReal]
  exact (Complex.ofReal_mul _ _).symm

end

end Work.GM.Affine
