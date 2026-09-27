import Mathlib
import Submission.Work.EKLComp.LeafAux
import Submission.Work.EKLRelCross.KappaApi

/-!
# The conditional measure of a subset of an atom, versus the measure of the atom

For a finite measure `ν` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a countably generated sub-σ-algebra
`𝔪.m ≤ borel X₃`, a point `x` and a measurable set `S ⊆ atom 𝔪.m x`, the conditional measure
`condExpKernel ν 𝔪.m x` of `S` and the `ν`-mass of the atom are related by

`condExpKernel ν 𝔪.m x S * ν (atom 𝔪.m x) = ν S`.

This is the exact ("pointwise", not merely almost-everywhere) form of the formula
`(κ x) S = ν S / ν [x]` for the conditional measure on the atom of `x`.

The proof has three ingredients.

* `condExpKernel_ae_eq_condExp` identifies the kernel value with the conditional probability
  `ν⟦S | 𝔪.m⟧` almost everywhere, so that the integral of `y ↦ (condExpKernel ν 𝔪.m y).real S`
  over the atom `A` can be evaluated by the defining property of the conditional expectation:
  `setIntegral_condExp` gives `∫ y in A, ν⟦S | 𝔪.m⟧ y ∂ν = ∫ y in A, 1_S y ∂ν = ν.real (A ∩ S)`.
* `kernel_atom_const` says the kernel is constant on atoms, so the same integral equals
  `ν.real A * (condExpKernel ν 𝔪.m x).real S`.
* Since `A ∩ S = S`, this gives the real identity
  `(condExpKernel ν 𝔪.m x).real S * ν.real A = ν.real S`, which is transported to `ℝ≥0∞`
  using `Measure.real_def` and `ENNReal.ofReal_toReal` (all the measures involved are finite:
  `ν` is finite and `condExpKernel ν 𝔪.m x` is a probability measure).
-/

open MeasureTheory
open scoped MeasureTheory ENNReal

set_option linter.unusedVariables false

namespace Work.EKLRelCross

theorem condExpKernel_atom_ratio (𝔪 : Work.EKLComp.SigAlg)
    [StandardBorelSpace Work.EKLContract.X3] (hm : 𝔪.m ≤ Work.EKLComp.borelX3)
    (hgen : ∃ b : Set (Set Work.EKLContract.X3), b.Countable ∧
      𝔪.m = MeasurableSpace.generateFrom b)
    (ν : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsFiniteMeasure ν]
    {x : Work.EKLContract.X3} {S : Set Work.EKLContract.X3} (hS : MeasurableSet S)
    (hSatom : S ⊆ Work.EKLContract.atom 𝔪.m x) :
    ProbabilityTheory.condExpKernel ν 𝔪.m x S *
      ν (Work.EKLContract.atom 𝔪.m x) = ν S := by
  classical
  set A : Set Work.EKLContract.X3 := Work.EKLContract.atom 𝔪.m x with hAdef
  have hgen' : Work.EKLComp.CountablyGen 𝔪.m := hgen
  have hAmeas' : MeasurableSet[𝔪.m] A := Work.EKLComp.measurableSet_atom 𝔪.m hgen' x
  have hAmeas : MeasurableSet A := hm A hAmeas'
  have hAS : A ∩ S = S := Set.inter_eq_right.mpr hSatom
  -- The kernel value at `y` is a version of the conditional probability `ν⟦S | 𝔪.m⟧`.
  have hae : (fun y => (ProbabilityTheory.condExpKernel ν 𝔪.m y).real S)
      =ᵐ[ν] MeasureTheory.condExp 𝔪.m ν (S.indicator fun _ => (1 : ℝ)) :=
    ProbabilityTheory.condExpKernel_ae_eq_condExp hm hS
  -- Its integral over the atom `A` is `ν (A ∩ S) = ν S`.
  have hint1 : ∫ y in A, (ProbabilityTheory.condExpKernel ν 𝔪.m y).real S ∂ν
      = ν.real (A ∩ S) := by
    rw [setIntegral_congr_ae hAmeas (hae.mono (fun y hy _ => hy))]
    rw [setIntegral_condExp hm ((integrable_const (1 : ℝ)).indicator hS) hAmeas']
    rw [← MeasureTheory.integral_indicator hAmeas]
    rw [Set.indicator_indicator]
    exact MeasureTheory.integral_indicator_one (hAmeas.inter hS)
  -- The kernel is constant on atoms, so the integral over `A` is also `ν A` times that value.
  have hconst : ∀ y ∈ A, (ProbabilityTheory.condExpKernel ν 𝔪.m y).real S
      = (ProbabilityTheory.condExpKernel ν 𝔪.m x).real S := fun y hy =>
    congrArg (fun μ : MeasureTheory.Measure Work.EKLContract.X3 => μ.real S)
      (Work.EKLComp.kernel_atom_const (𝔪 := 𝔪) hy).symm
  have hint2 : ∫ y in A, (ProbabilityTheory.condExpKernel ν 𝔪.m y).real S ∂ν
      = ν.real A * (ProbabilityTheory.condExpKernel ν 𝔪.m x).real S := by
    rw [setIntegral_congr_ae hAmeas (Filter.Eventually.of_forall fun y => fun hy => hconst y hy)]
    rw [setIntegral_const]
    rfl
  -- The real-valued identity.
  have hkey : (ProbabilityTheory.condExpKernel ν 𝔪.m x).real S * ν.real A = ν.real S := by
    rw [mul_comm, ← hint2, hint1, hAS]
  -- Finiteness of the two measures at the relevant sets.
  have hκfin : (ProbabilityTheory.condExpKernel ν 𝔪.m x) S ≠ ⊤ := by
    have hmarkov : ProbabilityTheory.IsMarkovKernel (ProbabilityTheory.condExpKernel ν 𝔪.m) :=
      inferInstance
    have h1 : (ProbabilityTheory.condExpKernel ν 𝔪.m x) Set.univ = 1 :=
      (hmarkov.isProbabilityMeasure x).measure_univ
    exact ne_top_of_le_ne_top (by rw [h1]; exact ENNReal.one_ne_top)
      (measure_mono (Set.subset_univ S))
  have hνAfin : ν A ≠ ⊤ := MeasureTheory.measure_ne_top ν A
  have hνSfin : ν S ≠ ⊤ := MeasureTheory.measure_ne_top ν S
  -- Transport the identity to `ℝ≥0∞`.
  have e1 : (ProbabilityTheory.condExpKernel ν 𝔪.m x) S
      = ENNReal.ofReal ((ProbabilityTheory.condExpKernel ν 𝔪.m x).real S) := by
    rw [MeasureTheory.Measure.real_def]
    exact (ENNReal.ofReal_toReal hκfin).symm
  have e2 : ν A = ENNReal.ofReal (ν.real A) := by
    rw [MeasureTheory.Measure.real_def]
    exact (ENNReal.ofReal_toReal hνAfin).symm
  have e3 : ν S = ENNReal.ofReal (ν.real S) := by
    rw [MeasureTheory.Measure.real_def]
    exact (ENNReal.ofReal_toReal hνSfin).symm
  have hmul : ENNReal.ofReal ((ProbabilityTheory.condExpKernel ν 𝔪.m x).real S)
        * ENNReal.ofReal (ν.real A)
      = ENNReal.ofReal ((ProbabilityTheory.condExpKernel ν 𝔪.m x).real S * ν.real A) :=
    (ENNReal.ofReal_mul (MeasureTheory.measureReal_nonneg
      (μ := ProbabilityTheory.condExpKernel ν 𝔪.m x) (s := S))).symm
  rw [e1, e2, e3, hmul, hkey]

end Work.EKLRelCross
