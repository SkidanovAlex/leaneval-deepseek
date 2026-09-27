import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances

/-!
# A measure carried by the support of another, from an integral identity

`SL₃(ℝ) = Matrix.SpecialLinearGroup (Fin 3) ℝ` is a locally compact, σ-compact,
pseudo-metrizable space (`Submission.Work.EKLRelCross.Instances`), so every measure on it
which is finite on compacts is regular.  Consequently the Riesz representation theorem
(`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`) applies: two such measures
agreeing on the integral of every compactly supported continuous real function are equal.

Here we apply this to a pair `μ`, `ρ` whose `C_c`-functionals differ by a positive factor `c`:
`μ = ENNReal.ofReal c • ρ`.  Hence `μ` is absolutely continuous with respect to `ρ`, so any set
which is `ρ`-null is `μ`-null.
-/

open MeasureTheory
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

theorem carried_of_integral_eq {μ ρ : MeasureTheory.Measure Work.EKLContract.SL3} (c : ℝ)
    (hc : 0 < c) (hμ : MeasureTheory.IsFiniteMeasureOnCompacts μ)
    (hρ : MeasureTheory.IsFiniteMeasureOnCompacts ρ)
    (h : ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ, ∫ g, f g ∂μ = c * ∫ g, f g ∂ρ)
    {s : Set Work.EKLContract.SL3} (hs : IsClosed s) (hρs : ρ sᶜ = 0) : μ sᶜ = 0 := by
  -- Both measures are locally finite, hence regular on the σ-compact, pseudo-metrizable
  -- locally compact space `SL₃(ℝ)`.
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts μ := hμ
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts ρ := hρ
  haveI : MeasureTheory.IsLocallyFiniteMeasure μ := inferInstance
  haveI : MeasureTheory.IsLocallyFiniteMeasure ρ := inferInstance
  haveI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  haveI : ρ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ρ
  haveI : (ENNReal.ofReal c • ρ).Regular := Measure.Regular.smul ENNReal.ofReal_ne_top
  -- The two measures are equal: their `C_c`-functionals agree.
  have h_eq : μ = ENNReal.ofReal c • ρ := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_smul_measure, ENNReal.toReal_ofReal hc.le, smul_eq_mul]
    exact h f
  -- Hence `μ` is carried by `ρ`.
  rw [h_eq, Measure.smul_apply, hρs, smul_zero]

end Work.EKLRelCross
