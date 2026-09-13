import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable

namespace Commons.Measure.Kernel

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal in
/-- For a σ-finite Borel measure `μ` on a second-countable metric space, the mass `μ (closedBall x ε)`
of a closed ball is a measurable function of its centre `x`.

This follows from measurability of the "parametrised section" map: the set
`{(x, y) | dist x y ≤ ε} ⊆ X × X` is closed (hence Borel), and `μ (closedBall x ε)` is the
`μ`-measure of its `x`-section. -/
theorem measurable_measure_closedBall {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] (μ : Measure X) [SFinite μ] (ε : ℝ) :
    Measurable fun x => μ (Metric.closedBall x ε) := by
  have hs : MeasurableSet {p : X × X | dist p.1 p.2 ≤ ε} := by
    have h : Measurable (fun p : X × X => dist p.1 p.2) := by fun_prop
    exact h measurableSet_Iic
  have h2 := measurable_measure_prodMk_left (ν := μ) hs
  simpa [Metric.closedBall, dist_comm] using h2

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal in
theorem aemeasurable_toReal_measure_closedBall {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure μ]
    (x₀ : EuclideanSpace ℝ (Fin n)) (ε : ℝ) :
    AEMeasurable (fun z => (μ (Metric.closedBall (x₀ + z) ε)).toReal) volume := by
  have h₁ : Measurable fun x : EuclideanSpace ℝ (Fin n) => μ (Metric.closedBall x ε) :=
    measurable_measure_closedBall μ ε
  have h₂ : Measurable fun z : EuclideanSpace ℝ (Fin n) => x₀ + z := by fun_prop
  exact ((h₁.comp h₂).ennreal_toReal).aemeasurable

end Commons.Measure.Kernel