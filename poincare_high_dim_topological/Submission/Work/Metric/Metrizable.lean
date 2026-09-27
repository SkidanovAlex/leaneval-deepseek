/-
Copyright (c) 2024 The poincare_high_dim_topological team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Work.Metric.Cover
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Compact charted spaces are second countable and metrizable

Let `M` be a charted space over a metric model space `E`.  If `M` is compact (and Hausdorff) and
`E` is second countable, then `M` is second countable, hence metrizable (Urysohn), hence carries a
compatible metric which we make explicit as `Work.Metric.metricOfCompact`.

This is step R1 of the engulfing proof of the high-dimensional Poincaré conjecture: the compact
homotopy sphere is a compact metrizable topological manifold, so it carries a metric in which
`ε`-arguments (Lebesgue numbers, small chart balls, mesh of covers) make sense.
-/

open Set Metric TopologicalSpace Filter

namespace Work.Metric

universe u v

variable {E : Type u} [PseudoMetricSpace E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]

/-- A compact charted space is σ-compact. -/
theorem sigmaCompactSpace_of_compactSpace [CompactSpace M] : SigmaCompactSpace M := inferInstance

/-- A charted space over a locally compact model space is locally compact. -/
theorem locallyCompactSpace_of_locallyCompactSpace [LocallyCompactSpace E] :
    LocallyCompactSpace M :=
  ChartedSpace.locallyCompactSpace E M

/-- A compact charted space over a second countable model space is second countable. -/
theorem secondCountableTopology_of_compactSpace [CompactSpace M] [SecondCountableTopology E] :
    SecondCountableTopology M := by
  haveI : SigmaCompactSpace M := inferInstance
  exact ChartedSpace.secondCountable_of_sigmaCompact E M

/-- A compact Hausdorff charted space over a second countable model space is metrizable
(Urysohn's metrization theorem). -/
theorem metrizableSpace_of_compactSpace [CompactSpace M] [T2Space M] [SecondCountableTopology E] :
    MetrizableSpace M := by
  haveI : SecondCountableTopology M := secondCountableTopology_of_compactSpace (E := E) (M := M)
  exact inferInstance

/-- A compact Hausdorff charted space is normal. -/
theorem normalSpace_of_compactSpace [CompactSpace M] [T2Space M] : NormalSpace M := inferInstance

/-- A compatible metric on a compact Hausdorff charted space over a second countable model space,
obtained from `MetrizableSpace`.  Its topology is the original topology, see
`Work.Metric.metricOfCompact_toTopologicalSpace`. -/
noncomputable abbrev metricOfCompact [CompactSpace M] [T2Space M]
    [SecondCountableTopology E] : MetricSpace M :=
  letI : MetrizableSpace M := metrizableSpace_of_compactSpace (E := E) (M := M)
  TopologicalSpace.metrizableSpaceMetric M

/-- The metric `Work.Metric.metricOfCompact` induces the original topology. -/
theorem metricOfCompact_toTopologicalSpace [CompactSpace M] [T2Space M] [SecondCountableTopology E] :
    (metricOfCompact (E := E) (M := M)).toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace M› := by
  with_reducible_and_instances rfl

end Work.Metric
