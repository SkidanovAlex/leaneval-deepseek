/-
Copyright (c) 2024 The poincare_high_dim_topological team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Work.Metric.Metrizable
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The metric facts for `ℝⁿ`-charted spaces

Specializations of the results of `Submission.Work.Metric.Metrizable` and
`Submission.Work.Metric.Cover` to a charted space `M` over `EuclideanSpace ℝ (Fin n)`, i.e. a
topological `n`-manifold.  These are the forms in which the engulfing development uses them.
The dimension `n` is the first explicit argument of each statement.

## Main results

For `M` a Hausdorff charted space over `EuclideanSpace ℝ (Fin n)`, with `[CompactSpace M]`:

* `Work.Metric.secondCountableTopology_euclideanSpace`
* `Work.Metric.metrizableSpace_euclideanSpace`
* `Work.Metric.normalSpace_euclideanSpace`
* `Work.Metric.metricOfCompactEuclideanSpace`, a compatible metric, with
  `Work.Metric.metricOfCompactEuclideanSpace_toTopologicalSpace`
* `Work.Metric.exists_chartBallCover_euclideanSpace`, a finite atlas of chart balls with
  closed-ball shrinkings.

With a metric on `M` in addition:

* `Work.Metric.exists_chartBallCover_diam_le_euclideanSpace`
* `Work.Metric.ChartBallCover.exists_pos_diam_lt_subset_euclideanSpace`
* `Work.Metric.exists_chartBallCover_diam_lebesgue_euclideanSpace`
-/

open Set Metric TopologicalSpace Filter

namespace Work.Metric

/-- A compact `n`-manifold is σ-compact. -/
theorem sigmaCompactSpace_euclideanSpace (n : ℕ) (M : Type*) [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M] :
    SigmaCompactSpace M :=
  sigmaCompactSpace_of_compactSpace

/-- A compact `n`-manifold is second countable. -/
theorem secondCountableTopology_euclideanSpace (n : ℕ) (M : Type*) [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M] :
    SecondCountableTopology M :=
  secondCountableTopology_of_compactSpace (E := EuclideanSpace ℝ (Fin n)) (M := M)

/-- A compact `n`-manifold is metrizable. -/
theorem metrizableSpace_euclideanSpace (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M] : MetrizableSpace M :=
  metrizableSpace_of_compactSpace (E := EuclideanSpace ℝ (Fin n)) (M := M)

/-- A compact `n`-manifold is normal. -/
theorem normalSpace_euclideanSpace (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M] : NormalSpace M :=
  normalSpace_of_compactSpace

/-- A compatible metric on a compact `n`-manifold, obtained from Urysohn's metrization theorem.
Use `letI : MetricSpace M := metricOfCompactEuclideanSpace n M` to install it. -/
noncomputable abbrev metricOfCompactEuclideanSpace (n : ℕ) (M : Type*) [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M] : MetricSpace M :=
  metricOfCompact (E := EuclideanSpace ℝ (Fin n)) (M := M)

/-- `Work.Metric.metricOfCompactEuclideanSpace` induces the original topology. -/
theorem metricOfCompactEuclideanSpace_toTopologicalSpace (n : ℕ) (M : Type*) [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M] :
    (metricOfCompactEuclideanSpace n M).toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace M› :=
  metricOfCompact_toTopologicalSpace (E := EuclideanSpace ℝ (Fin n)) (M := M)

/-- A closed chart ball in an `n`-manifold is compact. -/
theorem isCompact_chartClosedBall_euclideanSpace (n : ℕ) (M : Type*) [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {x : M} {r : ℝ}
    (h : Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin n)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) x).target) :
    IsCompact (chartClosedBall (E := EuclideanSpace ℝ (Fin n)) x r) :=
  isCompact_chartClosedBall h

/-- A compact `n`-manifold admits a finite atlas of chart balls with closed-ball shrinkings. -/
theorem exists_chartBallCover_euclideanSpace (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M] :
    Nonempty (ChartBallCover (EuclideanSpace ℝ (Fin n)) M) :=
  exists_chartBallCover (E := EuclideanSpace ℝ (Fin n)) (M := M)

/-- A compact `n`-manifold admits, for every `ε > 0`, a finite atlas of chart balls all of whose
members have diameter `≤ ε`. -/
theorem exists_chartBallCover_diam_le_euclideanSpace (n : ℕ) (M : Type*) [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ChartBallCover (EuclideanSpace ℝ (Fin n)) M,
      ∀ i, Metric.diam (chartBall (E := EuclideanSpace ℝ (Fin n)) (C.center i) (C.radius i)) ≤ ε :=
  exists_chartBallCover_diam_le (E := EuclideanSpace ℝ (Fin n)) (M' := M) hε

/-- **Lebesgue number lemma**, `n`-manifold form: for a finite atlas `C` of chart balls of a
compact `n`-manifold there is `δ > 0` such that every nonempty set of diameter `< δ` is contained
in one chart ball of `C`. -/
theorem ChartBallCover.exists_pos_diam_lt_subset_euclideanSpace (n : ℕ) (M : Type*) [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M]
    (C : ChartBallCover (EuclideanSpace ℝ (Fin n)) M) :
    ∃ δ > 0, ∀ S : Set M, S.Nonempty → Metric.diam S < δ →
      ∃ i, S ⊆ chartBall (E := EuclideanSpace ℝ (Fin n)) (C.center i) (C.radius i) :=
  C.exists_pos_diam_lt_subset

/-- A compact `n`-manifold admits, for every `ε > 0`, a finite atlas of chart balls with diameter
`≤ ε`, together with a Lebesgue number for it. -/
theorem exists_chartBallCover_diam_lebesgue_euclideanSpace (n : ℕ) (M : Type*) [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ChartBallCover (EuclideanSpace ℝ (Fin n)) M,
      (∀ i, Metric.diam (chartBall (E := EuclideanSpace ℝ (Fin n)) (C.center i) (C.radius i)) ≤ ε) ∧
      (∃ δ > 0, ∀ S : Set M, S.Nonempty → Metric.diam S < δ →
        ∃ i, S ⊆ chartBall (E := EuclideanSpace ℝ (Fin n)) (C.center i) (C.radius i)) :=
  exists_chartBallCover_diam_lebesgue (E := EuclideanSpace ℝ (Fin n)) (M' := M) hε

end Work.Metric
