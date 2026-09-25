import Mathlib
import Submission.Work.NN.Core.PertL2Defs

/-!
# The weighted measure `wMeas n φ` is finite on compact sets

`Work.NN.Core.wMeas n φ` is the weighted measure `e^{-φ} dz` on the flat model `ℂⁿ = Cn n`,
i.e. Lebesgue measure with density `z ↦ (Real.exp (-(φ z))).toNNReal`.  For a *continuous* weight
`φ : Cn n → ℝ` this density is a continuous, everywhere finite, `ℝ≥0`-valued function, so the
resulting measure is locally finite, hence finite on compact subsets.

The proof is the standard measure-theoretic argument: a continuous `ℝ≥0`-valued density with
respect to a locally finite measure gives a locally finite measure
(`IsLocallyFiniteMeasure.withDensity_coe`), and a locally finite measure is finite on compacts
(`isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`).  Both ingredients are Mathlib's; what is
recorded here is the specialisation to the weighted measure used by the `L²_φ` calculus of the
perturbed `∂̄`-solvability argument.
-/

open MeasureTheory Set
open scoped Topology ENNReal NNReal

namespace Work.NN.Core

/-- A measure with a continuous `ℝ≥0`-valued density with respect to a locally finite measure is
finite on compact sets. -/
lemma isFiniteMeasureOnCompacts_withDensity_of_continuous {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsLocallyFiniteMeasure μ]
    {f : X → ℝ≥0} (hf : Continuous f) :
    IsFiniteMeasureOnCompacts (μ.withDensity fun x => (f x : ℝ≥0∞)) :=
  @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ _
      (IsLocallyFiniteMeasure.withDensity_coe hf)

theorem wMeas_finiteOnCompacts {n : ℕ} {φ : Work.NN.Assemble.Cn n → ℝ}
    (hφ : Continuous φ) :
    MeasureTheory.IsFiniteMeasureOnCompacts (Work.NN.Core.wMeas n φ) := by
  rw [wMeas]
  exact isFiniteMeasureOnCompacts_withDensity_of_continuous
    (continuous_real_toNNReal.comp (Real.continuous_exp.comp hφ.neg))

end Work.NN.Core
