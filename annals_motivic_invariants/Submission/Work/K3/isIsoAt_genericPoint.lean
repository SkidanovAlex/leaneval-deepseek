import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.Motivic.exists_partialIso_toBirationalMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3

/-- Every birational map is an isomorphism at the generic point of its source: the generic point
of an irreducible scheme lies in every nonempty open, in particular in the (dense open) source of
any partial-isomorphism representative. -/
theorem isIsoAt_genericPoint {X Y : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (ψ : X.BirationalMap Y) :
    IsIsoAt ψ (genericPoint X) := by
  obtain ⟨i, hi⟩ := Work.Motivic.exists_partialIso_toBirationalMap ψ
  refine ⟨i, ?_, ?_⟩
  · exact ((genericPoint_spec X).mem_open_set_iff (U := (i.source : Set X)) i.source.2).mpr
      (by simpa using i.dense_source.nonempty)
  · rw [← AlgebraicGeometry.Scheme.PartialIso.toBirationalMap_hom, hi]

end Work.K3
