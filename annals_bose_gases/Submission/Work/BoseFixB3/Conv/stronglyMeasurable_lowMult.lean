import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.HighMass.OneBody
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Conv.stronglyMeasurable_lowMult`

For a measurable `Ψ : ℝ³ → ℝ`, the low-momentum multiplier
`Work.BoseBoxFix.lowMult fc κ ℓ Ψ` is strongly measurable.

`lowMult` is a momentum integral, so the proof is a single application of
`MeasureTheory.StronglyMeasurable.integral_prod_right` (which needs only joint strong
measurability of the integrand, NOT integrability — the Bochner integral is total):

  `(x,p) ↦ e^{i⟪p,x⟫} · f(‖p‖/κ) · kinFT(1_{acube ℓ}·Ψ) p`

is a product of three jointly strongly measurable factors:

* `(x,p) ↦ e^{i⟪p,x⟫}` — continuous;
* `(x,p) ↦ f(‖p‖/κ)` — continuous (`fc.smooth`, only depends on `p`);
* `(x,p) ↦ kinFT(1_{acube ℓ}·Ψ) p` — independent of `x`, and `p ↦ kinFT g p` is strongly
  measurable for measurable `g` because `kinFT g p = ∫_y e^{-i⟪p,y⟫}g(y)dy` is itself an
  integral of the jointly measurable kernel `(p,y) ↦ e^{-i⟪p,y⟫}g(y)`.

Then `.re` is continuous and the prefactor `(2π)⁻³` is a `const_mul`.

This is the `n = 1`/no-slot analogue of
`Work.BoseFixB3.Split.lowSlotStronglyMeasurable`, with the measurability hypothesis on `Ψ`
(the slot version assumes `Ψ` continuous because it needs the joint measurability of
`(x,z) ↦ 1_Λ(z)·Ψ(x_{j←z})`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.Conv

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The `p`-convention Fourier kernel `y ↦ e^{-i⟪p,y⟫}`. -/
private def fkern (p y : ℝ³) : ℂ := Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))

private lemma kinFT_eq_fkern (f : ℝ³ → ℂ) (p : ℝ³) :
    Submission.BoseGases.kinFT f p = ∫ y : ℝ³, fkern p y * f y := rfl

private lemma measurable_fkern : Measurable (fun w : ℝ³ × ℝ³ => fkern w.1 w.2) := by
  have hinner : Continuous (fun w : ℝ³ × ℝ³ => inner ℝ w.1 w.2) := continuous_inner
  exact Complex.continuous_exp.measurable.comp
    (continuous_neg.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hinner))).measurable

/-- The Fourier transform of a measurable function is strongly measurable (unconditional:
no integrability is needed, the Bochner integral is total). -/
private lemma stronglyMeasurable_kinFT {g : ℝ³ → ℂ} (hg : Measurable g) :
    StronglyMeasurable (fun p : ℝ³ => Submission.BoseGases.kinFT g p) := by
  have hfun : (fun p : ℝ³ => Submission.BoseGases.kinFT g p)
      = fun p : ℝ³ => ∫ y : ℝ³, fkern p y * g y := by
    funext p
    exact kinFT_eq_fkern g p
  rw [hfun]
  refine StronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ³))
    (f := fun w : ℝ³ × ℝ³ => fkern w.1 w.2 * g w.2) ?_
  exact measurable_fkern.stronglyMeasurable.mul (hg.comp measurable_snd).stronglyMeasurable

theorem stronglyMeasurable_lowMult {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    {Ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hΨm : Measurable Ψ) :
    MeasureTheory.StronglyMeasurable (fun x : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseBoxFix.lowMult fc κ ℓ Ψ x) := by
  -- the box-restricted `Ψ`, as a complex-valued function
  have hg : Measurable (fun z : ℝ³ =>
      (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (hΨm.indicator (Submission.BoseGases.acube_measurable ℓ))
  have hC : StronglyMeasurable (fun p : ℝ³ => Submission.BoseGases.kinFT (fun z : ℝ³ =>
      (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p) :=
    stronglyMeasurable_kinFT hg
  -- the three jointly strongly measurable factors of the `(x,p)`-integrand
  have hA : StronglyMeasurable (fun w : ℝ³ × ℝ³ =>
      Complex.exp (Complex.I * (inner ℝ w.2 w.1 : ℂ))) := by
    have hcont : Continuous (fun w : ℝ³ × ℝ³ => inner ℝ w.2 w.1) :=
      continuous_inner.comp (continuous_snd.prodMk continuous_fst)
    exact (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hcont))).measurable.stronglyMeasurable
  have hB : StronglyMeasurable (fun w : ℝ³ × ℝ³ => ((fc.f (‖w.2‖ / κ) : ℝ) : ℂ)) := by
    have hcont : Continuous (fun w : ℝ³ × ℝ³ => fc.f (‖w.2‖ / κ)) :=
      fc.smooth.continuous.comp ((continuous_norm.comp continuous_snd).div_const κ)
    exact (Complex.continuous_ofReal.comp hcont).measurable.stronglyMeasurable
  have hC' : StronglyMeasurable (fun w : ℝ³ × ℝ³ =>
      Submission.BoseGases.kinFT (fun z : ℝ³ =>
        (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) w.2) :=
    hC.comp_measurable measurable_snd
  have hjoint : StronglyMeasurable (fun w : ℝ³ × ℝ³ =>
      Complex.exp (Complex.I * (inner ℝ w.2 w.1 : ℂ)) * ((fc.f (‖w.2‖ / κ) : ℝ) : ℂ) *
        Submission.BoseGases.kinFT (fun z : ℝ³ =>
          (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) w.2) :=
    (hA.mul hB).mul hC'
  -- integrate in the momentum variable `p`
  have hint : StronglyMeasurable (fun x : ℝ³ => ∫ p : ℝ³,
      Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
        Submission.BoseGases.kinFT (fun z : ℝ³ =>
          (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p) :=
    hjoint.integral_prod_right (ν := (volume : Measure ℝ³))
  have hcm : StronglyMeasurable (fun x : ℝ³ =>
      ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) * ∫ p : ℝ³,
        Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
          Submission.BoseGases.kinFT (fun z : ℝ³ =>
            (((Submission.BoseGases.acube ℓ).indicator Ψ z : ℝ) : ℂ)) p) :=
    hint.const_mul _
  simpa only [Work.BoseBoxFix.lowMult]
    using Complex.continuous_re.comp_stronglyMeasurable hcm

end Work.BoseFixB3.Conv
