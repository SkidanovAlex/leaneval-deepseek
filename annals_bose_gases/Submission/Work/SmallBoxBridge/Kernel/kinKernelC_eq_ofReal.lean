import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxBridge.Defs
import Submission.Work.SmallBoxBridge.Kernel.radialCosIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `kinKernelC F z = (kinKernel F z : ℂ)` — the kernel `K_F = 𝓕⁻¹F` is real

`kinKernelC F z` is the complex (`e^{i⟪p,z⟫}`) version of the inverse Fourier transform of
the radial symbol `p ↦ F ‖p‖`, while `kinKernel F z` is the real (`cos⟪p,z⟫`) version.
The identity holds without any hypothesis on `F` (in particular for non-integrable
symbols, where both Bochner integrals are `0` by convention).

The proof splits the complex phase into real and imaginary parts:
`↑(F‖p‖)·e^{i⟪p,z⟫} = ↑(F‖p‖·cos⟪p,z⟫) + I·↑(F‖p‖·sin⟪p,z⟫)`, uses the oddness of
`p ↦ F‖p‖·sin⟪p,z⟫` (its integral vanishes: `∫ f(-p) = ∫ f p` and `f(-p) = -f p`) and the
fact that the real-valued integral is the real part of the complex one.  The latter is
`integral_ofReal`, valid with no integrability hypothesis.  The only place where
integrability matters is the additivity of the Bochner integral: it is used when the
cosine-factor is integrable, and then *radiality* forces the whole phase-function to be
integrable (`radialCosIntegrable`, proved in
`Submission/Work/SmallBoxBridge/Kernel/radialCosIntegrable.lean`).  If instead the cosine
factor is non-integrable, both integrals are `0` by `integral_undef`.
-/

namespace Work.SmallBoxBridge.Kernel

open MeasureTheory
open scoped Real BigOperators

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Splitting the complex phase into its real and imaginary parts. -/
private lemma cos_sin_decomp (F : ℝ → ℝ) (z : ℝ³) (p : ℝ³) :
    (F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ))
      = ((F ‖p‖ * Real.cos (inner ℝ p z) : ℝ) : ℂ)
        + Complex.I * ((F ‖p‖ * Real.sin (inner ℝ p z) : ℝ) : ℂ) := by
  have hI : Complex.exp (Complex.I * (inner ℝ p z : ℂ))
      = ((Real.cos (inner ℝ p z) : ℂ)) + ((Real.sin (inner ℝ p z) : ℂ)) * Complex.I := by
    rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hI]
  push_cast
  ring

/-- The real part of the complex phase is the radial cosine kernel. -/
private lemma cos_re_decomp (F : ℝ → ℝ) (z : ℝ³) (p : ℝ³) :
    ((F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ))).re
      = F ‖p‖ * Real.cos (inner ℝ p z) := by
  rw [cos_sin_decomp F z p, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- `p ↦ F ‖p‖ · sin ⟪p,z⟫` is odd, hence has vanishing (Bochner) integral. -/
private lemma integral_radial_sin_zero (F : ℝ → ℝ) (z : ℝ³) :
    (∫ p : ℝ³, F ‖p‖ * Real.sin (inner ℝ p z)) = 0 := by
  have hodd : ∀ p : ℝ³, F ‖(-p)‖ * Real.sin (inner ℝ (-p) z)
      = -(F ‖p‖ * Real.sin (inner ℝ p z)) := by
    intro p
    simp [Real.sin_neg]
  have h1 := integral_neg_eq_self (fun p : ℝ³ => F ‖p‖ * Real.sin (inner ℝ p z)) volume
  simp only [hodd] at h1
  rw [integral_neg] at h1
  linarith

/-- If the complex phase is integrable then its real part is (the cosine factor). -/
private lemma integrable_cos_of_integrable_complex (F : ℝ → ℝ) (z : ℝ³)
    (hw : Integrable fun p : ℝ³ => (F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ))) :
    Integrable fun p : ℝ³ => F ‖p‖ * Real.cos (inner ℝ p z) := by
  have hre : (fun p : ℝ³ => ((F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ))).re)
      = fun p : ℝ³ => F ‖p‖ * Real.cos (inner ℝ p z) :=
    funext fun p => cos_re_decomp F z p
  rw [← hre]
  exact hw.re

/-- The main computation, in the case where the radial symbol is integrable: then the
complex phase, its real and its imaginary parts are all integrable and the Bochner
integral is additive. -/
private lemma key_of_integrable (F : ℝ → ℝ) (z : ℝ³)
    (hG : Integrable fun p : ℝ³ => F ‖p‖) :
    (∫ p : ℝ³, (F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ)))
      = ((∫ p : ℝ³, F ‖p‖ * Real.cos (inner ℝ p z) : ℝ) : ℂ) := by
  have hbddc : ∀ᵐ p : ℝ³, ‖Real.cos (inner ℝ p z)‖ ≤ 1 :=
    Filter.Eventually.of_forall fun p => by
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (inner ℝ p z)
  have hbdds : ∀ᵐ p : ℝ³, ‖Real.sin (inner ℝ p z)‖ ≤ 1 :=
    Filter.Eventually.of_forall fun p => by
      simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (inner ℝ p z)
  have hh : Integrable fun p : ℝ³ => F ‖p‖ * Real.cos (inner ℝ p z) :=
    hG.mul_bdd (by fun_prop) hbddc
  have hs : Integrable fun p : ℝ³ => F ‖p‖ * Real.sin (inner ℝ p z) :=
    hG.mul_bdd (by fun_prop) hbdds
  have hw : Integrable fun p : ℝ³ => (F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ)) := by
    refine (hG.ofReal).mul_bdd (c := 1) (by fun_prop) ?_
    filter_upwards with p
    simpa [mul_comm Complex.I] using
      le_of_eq (Complex.norm_exp_ofReal_mul_I (inner ℝ p z))
  have hcongr : (∫ p : ℝ³, (F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ)))
      = ∫ p : ℝ³, (((F ‖p‖ * Real.cos (inner ℝ p z) : ℝ) : ℂ)
          + Complex.I * ((F ‖p‖ * Real.sin (inner ℝ p z) : ℝ) : ℂ)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => cos_sin_decomp F z p)
  rw [hcongr]
  rw [show (∫ p : ℝ³, (((F ‖p‖ * Real.cos (inner ℝ p z) : ℝ) : ℂ)
          + Complex.I * ((F ‖p‖ * Real.sin (inner ℝ p z) : ℝ) : ℂ)))
        = (∫ p : ℝ³, (((F ‖p‖ * Real.cos (inner ℝ p z) : ℝ) : ℂ)))
          + ∫ p : ℝ³, Complex.I * (((F ‖p‖ * Real.sin (inner ℝ p z) : ℝ) : ℂ))
      from integral_add hh.ofReal (hs.ofReal.const_mul Complex.I)]
  rw [integral_const_mul]
  rw [show (∫ p : ℝ³, ((F ‖p‖ * Real.cos (inner ℝ p z) : ℝ) : ℂ))
        = ((∫ p : ℝ³, F ‖p‖ * Real.cos (inner ℝ p z) : ℝ) : ℂ) from integral_ofReal]
  rw [show (∫ p : ℝ³, ((F ‖p‖ * Real.sin (inner ℝ p z) : ℝ) : ℂ))
        = ((∫ p : ℝ³, F ‖p‖ * Real.sin (inner ℝ p z) : ℝ) : ℂ) from integral_ofReal]
  rw [integral_radial_sin_zero F z]
  simp

/-- The target identity, from the radial integrability input `crux`. -/
theorem kinKernelC_eq_ofReal_of_crux
    (crux : ∀ (F : ℝ → ℝ) (z : ℝ³),
      Integrable (fun p : ℝ³ => F ‖p‖ * Real.cos (inner ℝ p z)) →
        Integrable (fun p : ℝ³ => F ‖p‖))
    (F : ℝ → ℝ) (z : ℝ³) :
    Submission.BoseGases.kinKernelC F z = (Submission.BoseGases.kinKernel F z : ℂ) := by
  unfold Submission.BoseGases.kinKernelC Submission.BoseGases.kinKernel
  rw [Complex.ofReal_mul]
  congr 1
  by_cases hh : Integrable fun p : ℝ³ => F ‖p‖ * Real.cos (inner ℝ p z)
  · exact key_of_integrable F z (crux F z hh)
  · have hw : ¬ Integrable fun p : ℝ³ =>
        (F ‖p‖ : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ)) :=
      fun hwi => hh (integrable_cos_of_integrable_complex F z hwi)
    rw [integral_undef hw, integral_undef hh]
    simp

theorem kinKernelC_eq_ofReal (F : ℝ → ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinKernelC F z = (Submission.BoseGases.kinKernel F z : ℂ) :=
  kinKernelC_eq_ofReal_of_crux (fun F z h => radialCosIntegrable F z h) F z

end Work.SmallBoxBridge.Kernel
