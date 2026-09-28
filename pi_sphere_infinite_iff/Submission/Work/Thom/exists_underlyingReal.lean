import Mathlib
import Submission.Work.TangentClasses.Bundle

namespace Work.Thom

/-- Every complex vector bundle (in the gluing-data model, `VectorBundleCore ℂ B F ι`) restricts
to a real vector bundle on the same base with the same fibres: the underlying real bundle.  The
witness has the same cover `baseSet`, the same `indexAt`, and the same transition functions
(viewed as real-linear maps by restriction of scalars along `ℝ → ℂ`). -/
theorem exists_underlyingReal {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℂ F] {ι : Type} (Z : VectorBundleCore ℂ B F ι) :
    ∃ Z' : VectorBundleCore ℝ B F ι, Z'.baseSet = Z.baseSet ∧ Z'.indexAt = Z.indexAt ∧
      (∀ (i j : ι) (b : B), ⇑(Z'.coordChange i j b) = ⇑(Z.coordChange i j b)) := by
  refine ⟨{ baseSet := Z.baseSet
            isOpen_baseSet := Z.isOpen_baseSet
            indexAt := Z.indexAt
            mem_baseSet_at := Z.mem_baseSet_at
            coordChange := fun i j b => (Z.coordChange i j b).restrictScalars ℝ
            coordChange_self := ?_
            continuousOn_coordChange := ?_
            coordChange_comp := ?_ }, rfl, rfl, fun i j b => rfl⟩
  · intro i x hx v
    exact Z.coordChange_self i x hx v
  · intro i j
    exact (ContinuousLinearMap.continuous_restrictScalars (𝕜 := ℂ) (E := F) (F := F) ℝ).comp_continuousOn
      (Z.continuousOn_coordChange i j)
  · intro i j k x hx v
    exact Z.coordChange_comp i j k x hx v

end Work.Thom
