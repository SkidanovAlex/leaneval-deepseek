import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Momentum.nsqAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.nsq_stronglyMeasurable_PsiC`

Strong measurability of the mean-free localised state
`PsiC ℓ p ψ = boxFTfun ℓ p ψ − boxMeanR ℓ ψ · boxHat ℓ p`.

Both ingredients are box-localised shifted integrals `x ↦ ∫_{z ∈ acube ℓ} c z · g (x+z)`:

* `boxFTfun ℓ p ψ` with `c z = exp(−i⟪p,z⟫)` and `g = ψ` (complexified);
* `boxMeanR ℓ ψ` with `c = 1` and `g = ψ` (real-valued).

`nsqAux.nsq_stronglyMeasurable_shiftIntegral` covers the complex case; the real case is the
helper `nsq_stronglyMeasurable_shiftIntegral_real` below.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Real-valued analogue of `nsq_stronglyMeasurable_shiftIntegral`: for a strongly
measurable `g : ℝ³ → ℝ`, the box-localised shifted integral `x ↦ ∫_{z ∈ acube ℓ} g (x+z)`
is strongly measurable. -/
lemma nsq_stronglyMeasurable_shiftIntegral_real (ℓ : ℝ) (g : ℝ³ → ℝ)
    (hg : StronglyMeasurable g) :
    StronglyMeasurable (fun x : ℝ³ => ∫ z in acube ℓ, g (x + z)) := by
  have hmul : StronglyMeasurable (fun q : ℝ³ × ℝ³ => g (q.1 + q.2)) :=
    hg.comp_measurable (measurable_fst.add measurable_snd)
  exact StronglyMeasurable.integral_prod_right' (ν := volume.restrict (acube ℓ)) hmul

/-- The box mean `boxMeanR ℓ ψ` is strongly measurable as soon as `ψ` is. -/
lemma nsq_stronglyMeasurable_boxMeanR (ℓ : ℝ) (ψ : ℝ³ → ℝ) (hψ : StronglyMeasurable ψ) :
    StronglyMeasurable (boxMeanR ℓ ψ) := by
  have h : StronglyMeasurable (fun x : ℝ³ => (ℓ ^ 3)⁻¹ * ∫ z in acube ℓ, ψ (x + z)) :=
    (nsq_stronglyMeasurable_shiftIntegral_real ℓ ψ hψ).const_mul ((ℓ ^ 3)⁻¹)
  exact h

/-- `boxFTfun ℓ p ψ` is strongly measurable as soon as `ψ` is (it is a box-localised
shifted integral of the continuous function `z ↦ exp(−i⟪p,z⟫)` against `ψ`). -/
lemma nsq_stronglyMeasurable_boxFTfun (ℓ : ℝ) (p : ℝ³) (ψ : ℝ³ → ℝ)
    (hψ : StronglyMeasurable ψ) : StronglyMeasurable (boxFTfun ℓ p ψ) := by
  have hc : StronglyMeasurable
      (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) := by
    refine (Complex.continuous_exp.comp ?_).stronglyMeasurable
    exact (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))).neg
  have hg : StronglyMeasurable (fun y : ℝ³ => ((ψ y : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp_stronglyMeasurable hψ)
  unfold boxFTfun
  exact nsq_stronglyMeasurable_shiftIntegral ℓ _ _ hc hg

theorem nsq_stronglyMeasurable_PsiC (ℓ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) : MeasureTheory.StronglyMeasurable (Work.BoseKinLoc.Momentum.PsiC ℓ p ψ) := by
  have hmeas : StronglyMeasurable ψ := hψ.continuous.stronglyMeasurable
  have hFT : StronglyMeasurable (boxFTfun ℓ p ψ) := nsq_stronglyMeasurable_boxFTfun ℓ p ψ hmeas
  have hBM : StronglyMeasurable (fun x : ℝ³ => (boxMeanR ℓ ψ x : ℂ)) :=
    Complex.continuous_ofReal.stronglyMeasurable.comp_measurable
      (nsq_stronglyMeasurable_boxMeanR ℓ ψ hmeas).measurable
  have hBMc : StronglyMeasurable
      (fun x : ℝ³ => (boxMeanR ℓ ψ x : ℂ) * (Work.OneBodyKin.boxHat ℓ p : ℂ)) :=
    hBM.mul stronglyMeasurable_const
  exact hFT.sub hBMc

end Work.BoseKinLoc.Momentum
