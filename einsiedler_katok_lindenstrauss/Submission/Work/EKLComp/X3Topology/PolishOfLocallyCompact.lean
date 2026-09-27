import Mathlib
import Submission.Work.EKLComp.X3Topology.SecondCountableOnePoint

namespace Work.EKLComp.X3Topology

open TopologicalSpace Set Filter

/-- A compact Hausdorff space with second countable topology is Polish: it is metrizable by
Urysohn's metrization theorem, and any compact space is complete for the uniformity induced by a
compatible metric. -/
theorem polishSpace_of_compact_t2_secondCountable (K : Type*) [TopologicalSpace K] [CompactSpace K]
    [T2Space K] [SecondCountableTopology K] : PolishSpace K := by
  haveI : MetrizableSpace K := inferInstance
  letI := TopologicalSpace.pseudoMetrizableSpaceUniformity K
  haveI : IsCountablyGenerated (uniformity K) :=
    TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated K
  haveI : CompleteSpace K :=
    completeSpace_iff_isComplete_univ.2 isCompact_univ.isComplete
  infer_instance

theorem PolishOfLocallyCompact (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [T2Space X] : PolishSpace X := by
  -- The one point compactification of `X` is compact, Hausdorff and second countable.
  haveI : SecondCountableTopology (OnePoint X) := SecondCountableOnePoint X
  haveI : PolishSpace (OnePoint X) :=
    polishSpace_of_compact_t2_secondCountable (OnePoint X)
  -- `X` is an open subset of `OnePoint X` (namely the complement of `∞`).
  have hs : IsOpen (range ((↑) : X → OnePoint X)) := OnePoint.isOpen_range_coe
  haveI : PolishSpace (range ((↑) : X → OnePoint X)) := hs.polishSpace
  -- Transfer the Polish structure back to `X` along the canonical homeomorphism.
  let e : X ≃ range ((↑) : X → OnePoint X) := Equiv.ofInjective _ OnePoint.coe_injective
  have hP := Equiv.polishSpace_induced e
  have htop : (inferInstance : TopologicalSpace (range ((↑) : X → OnePoint X))).induced (e : X → _)
      = ‹TopologicalSpace X› := by
    rw [show (inferInstance : TopologicalSpace (range ((↑) : X → OnePoint X)))
        = (inferInstance : TopologicalSpace (OnePoint X)).induced Subtype.val from rfl]
    rw [induced_compose]
    rw [show ((Subtype.val : range ((↑) : X → OnePoint X) → OnePoint X) ∘ (e : X → _))
        = OnePoint.some from rfl]
    exact ((OnePoint.isOpenEmbedding_coe (X := X)).isEmbedding.toIsInducing).eq_induced.symm
  exact htop ▸ hP

end Work.EKLComp.X3Topology
