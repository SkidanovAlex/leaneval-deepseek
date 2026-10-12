import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SmallBoxBridge.Kernel.integral_sin_inner_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `kinKernelC F z = (kinKernel F z : ℂ)` under radial integrability

`kinKernelC F z = (2π)⁻³∫_p F‖p‖·e^{i⟪p,z⟫}dp` is the complex (`e^{i⟪p,·⟫}`) form of the
kernel of the radial symbol `p ↦ F‖p‖`, while `kinKernel F z = (2π)⁻³∫_p F‖p‖·cos⟪p,z⟫dp`
is its real (`cos`) form.  The two agree because the sine part of the phase is odd, hence
integrates to `0` (`Work.SmallBoxBridge.Kernel.integral_sin_inner_eq_zero`).

Here we prove this in the case where the *radial* symbol is integrable
(`hF : Integrable (fun p => F ‖p‖)`); this is the hypothesis under which the bridge needs the
identity.  The splitting of the complex Bochner integral into its real part, plus the
imaginary part `I·∫_p F‖p‖·sin⟪p,z⟫`, needs the additivity of the Bochner integral, so both
`F‖p‖cos⟪p,z⟫` and `F‖p‖sin⟪p,z⟫` must be integrable — they are dominated by `|F‖p‖|`,
which `hF` makes integrable.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real BigOperators

namespace Work.SmallBoxBridge.Resolve

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Pointwise split of the complex phase into its real and imaginary parts:
`↑(F‖p‖)·e^{i⟪p,z⟫} = ↑(F‖p‖cos⟪p,z⟫) + I·↑(F‖p‖sin⟪p,z⟫)`. -/
private lemma exp_I_inner_decomp (F : ℝ → ℝ) (z p : ℝ³) :
    (F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ))
      = ((F ‖p‖ * Real.cos (inner ℝ p z) : ℝ) : ℂ)
        + Complex.I * ((F ‖p‖ * Real.sin (inner ℝ p z) : ℝ) : ℂ) := by
  have hI : Complex.exp (Complex.I * (inner ℝ p z : ℂ))
      = ((Real.cos (inner ℝ p z) : ℂ)) + ((Real.sin (inner ℝ p z) : ℂ)) * Complex.I := by
    rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hI]; push_cast; ring

/-- The complex phase integral is the complexification of the real cosine kernel integral. -/
private lemma integral_complex_exp_eq_ofReal_cos (F : ℝ → ℝ)
    (hF : Integrable (fun p : ℝ³ => F ‖p‖)) (z : ℝ³) :
    (∫ p : ℝ³, (F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ)))
      = ((∫ p : ℝ³, F ‖p‖ * Real.cos (inner ℝ p z) : ℝ) : ℂ) := by
  have hbddc : ∀ᵐ p : ℝ³, ‖Real.cos (inner ℝ p z)‖ ≤ 1 :=
    Eventually.of_forall fun p => by
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (inner ℝ p z)
  have hbdds : ∀ᵐ p : ℝ³, ‖Real.sin (inner ℝ p z)‖ ≤ 1 :=
    Eventually.of_forall fun p => by
      simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (inner ℝ p z)
  have hh : Integrable fun p : ℝ³ => F ‖p‖ * Real.cos (inner ℝ p z) :=
    hF.mul_bdd (by fun_prop) hbddc
  have hs : Integrable fun p : ℝ³ => F ‖p‖ * Real.sin (inner ℝ p z) :=
    hF.mul_bdd (by fun_prop) hbdds
  -- split the phase pointwise
  have hcongr : (∫ p : ℝ³, (F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ)))
      = ∫ a : ℝ³, ((F ‖a‖ * Real.cos (inner ℝ a z) : ℝ) : ℂ)
          + Complex.I * ((F ‖a‖ * Real.sin (inner ℝ a z) : ℝ) : ℂ) :=
    integral_congr_ae (μ := volume)
      (Eventually.of_forall fun p => exp_I_inner_decomp F z p)
  -- additivity of the Bochner integral
  have hadd : (∫ a : ℝ³, ((F ‖a‖ * Real.cos (inner ℝ a z) : ℝ) : ℂ)
          + Complex.I * ((F ‖a‖ * Real.sin (inner ℝ a z) : ℝ) : ℂ))
      = (∫ a : ℝ³, ((F ‖a‖ * Real.cos (inner ℝ a z) : ℝ) : ℂ))
        + ∫ a : ℝ³, Complex.I * ((F ‖a‖ * Real.sin (inner ℝ a z) : ℝ) : ℂ) :=
    integral_add hh.ofReal (hs.ofReal.const_mul Complex.I)
  -- the real-valued integrals are the complexifications of the real ones
  have h1 : (∫ a : ℝ³, ((F ‖a‖ * Real.cos (inner ℝ a z) : ℝ) : ℂ))
      = ((∫ a : ℝ³, F ‖a‖ * Real.cos (inner ℝ a z) : ℝ) : ℂ) :=
    integral_ofReal (𝕜 := ℂ)
  have h2 : (∫ a : ℝ³, Complex.I * ((F ‖a‖ * Real.sin (inner ℝ a z) : ℝ) : ℂ))
      = Complex.I * ((∫ a : ℝ³, F ‖a‖ * Real.sin (inner ℝ a z) : ℝ) : ℂ) := by
    rw [integral_const_mul]
    exact congrArg (fun w : ℂ => Complex.I * w) (integral_ofReal (𝕜 := ℂ))
  -- the sine part vanishes by oddness
  have h3 : (∫ a : ℝ³, F ‖a‖ * Real.sin (inner ℝ a z)) = 0 :=
    Work.SmallBoxBridge.Kernel.integral_sin_inner_eq_zero F z
  rw [hcongr, hadd, h1, h2, h3]
  simp

theorem kinKernelC_eq_ofReal_aux (F : ℝ → ℝ)
    (hF : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinKernelC F z = (Submission.BoseGases.kinKernel F z : ℂ) := by
  have key : (∫ p : ℝ³, (F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ)))
      = ((∫ p : ℝ³, F ‖p‖ * Real.cos (inner ℝ p z) : ℝ) : ℂ) :=
    integral_complex_exp_eq_ofReal_cos F hF z
  unfold Submission.BoseGases.kinKernelC Submission.BoseGases.kinKernel
  rw [key, Complex.ofReal_mul]

end Work.SmallBoxBridge.Resolve
