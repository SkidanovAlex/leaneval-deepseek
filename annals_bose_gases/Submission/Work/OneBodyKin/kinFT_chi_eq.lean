import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.kinFT_chi_eq`

The `p`-convention Fourier transform of the bump `χ` is the real cosine profile `profHat`:

    `kinFT (χ : ℝ³ → ℂ) p = (profHat p : ℂ)`.

Both sides are the integral `∫_z χ z · e^{−i⟪p,z⟫} dz`.  Splitting `e^{−i θ} = cos θ − i sin θ`
into real and imaginary parts, the real part is exactly `∫_z χ z cos⟪p,z⟫ dz = profHat p`,
while the imaginary part is `−∫_z χ z sin⟪p,z⟫ dz`, which vanishes because the integrand is odd:
`χ` is even, `sin` is odd and `z ↦ ⟪p,z⟫` is odd, so the substitution `z ↦ −z` (Lebesgue measure
is negation invariant) turns the integral into its own negative.
-/

noncomputable section

open MeasureTheory

namespace Work.OneBodyKin

open Submission.BoseGases

set_option maxHeartbeats 800000
set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The Fourier transform of the bump equals its real cosine profile.**  Since `χ` is even, the
sine part of `kinFT (χ : ℝ³ → ℂ)` vanishes, leaving the real profile `profHat`. -/
theorem kinFT_chi_eq (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chi z : ℂ)) p
      = (Work.OneBodyKin.profHat p : ℂ) := by
  -- the integrand `z ↦ e^{−i⟪p,z⟫} χ z` is continuous and compactly supported, hence integrable
  have hcont : Continuous (fun y : ℝ³ =>
      Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (chi y : ℂ)) := by
    apply Continuous.mul
    · apply Complex.continuous_exp.comp
      apply Continuous.neg
      apply Continuous.mul continuous_const
      exact Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)
    · exact Complex.continuous_ofReal.comp chi_continuous
  have hcs : HasCompactSupport (fun y : ℝ³ =>
      Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (chi y : ℂ)) := by
    refine chi_hasCompactSupport.mono (fun y hy => ?_)
    intro hchi
    exact hy (by simp [hchi])
  have hf : Integrable (fun y : ℝ³ =>
      Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (chi y : ℂ)) volume :=
    hcont.integrable_of_hasCompactSupport hcs
  -- expansion of the exponential into its real and imaginary parts
  have hexp : ∀ y : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
      = ((Real.cos (inner ℝ p y) : ℝ) : ℂ) - ((Real.sin (inner ℝ p y) : ℝ) : ℂ) * Complex.I := by
    intro y
    rw [show -(Complex.I * ((inner ℝ p y : ℝ) : ℂ))
          = ((-(inner ℝ p y) : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hpt : ∀ y : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (chi y : ℂ)
      = ((chi y * Real.cos (inner ℝ p y) : ℝ) : ℂ)
        + ((-(chi y * Real.sin (inner ℝ p y)) : ℝ) : ℂ) * Complex.I := by
    intro y
    rw [hexp y]
    push_cast
    ring
  have hre_pt : ∀ y : ℝ³, (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (chi y : ℂ)).re = chi y * Real.cos (inner ℝ p y) := by
    intro y
    rw [hpt y]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him_pt : ∀ y : ℝ³, (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ)))
        * (chi y : ℂ)).im = -(chi y * Real.sin (inner ℝ p y)) := by
    intro y
    rw [hpt y]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [kinFT]
  change (∫ y : ℝ³, Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (chi y : ℂ))
    = (profHat p : ℂ)
  apply Complex.ext
  · -- real part
    have hre : (∫ y : ℝ³,
          Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (chi y : ℂ)).re
        = ∫ y : ℝ³,
          (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (chi y : ℂ)).re := by
      have := ContinuousLinearMap.integral_comp_comm Complex.reCLM hf
      simpa using this.symm
    rw [hre]
    rw [show (∫ y : ℝ³,
            (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (chi y : ℂ)).re)
          = ∫ y : ℝ³, chi y * Real.cos (inner ℝ p y) from by
      apply integral_congr_ae
      exact MeasureTheory.ae_of_all _ hre_pt]
    simp [profHat]
  · -- imaginary part
    have him : (∫ y : ℝ³,
          Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (chi y : ℂ)).im
        = ∫ y : ℝ³,
          (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (chi y : ℂ)).im := by
      have := ContinuousLinearMap.integral_comp_comm Complex.imCLM hf
      simpa using this.symm
    rw [him]
    rw [show (∫ y : ℝ³,
            (Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) * (chi y : ℂ)).im)
          = ∫ y : ℝ³, -(chi y * Real.sin (inner ℝ p y)) from by
      apply integral_congr_ae
      exact MeasureTheory.ae_of_all _ him_pt]
    rw [MeasureTheory.integral_neg]
    -- the odd integral vanishes
    have hzero : (∫ y : ℝ³, chi y * Real.sin (inner ℝ p y)) = 0 := by
      have hinv := MeasureTheory.integral_neg_eq_self
        (fun y : ℝ³ => chi y * Real.sin (inner ℝ p y)) (volume : Measure ℝ³)
      have hshift : (∫ y : ℝ³, (fun y : ℝ³ => chi y * Real.sin (inner ℝ p y)) (-y))
          = -(∫ y : ℝ³, chi y * Real.sin (inner ℝ p y)) := by
        rw [← MeasureTheory.integral_neg]
        apply integral_congr_ae
        exact MeasureTheory.ae_of_all _ (fun y => by
          simp only [inner_neg_right, Real.sin_neg, chi_even]
          ring)
      rw [hshift] at hinv
      linarith
    rw [hzero, neg_zero]
    simp

end Work.OneBodyKin
