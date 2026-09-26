import Mathlib
import Submission.Work.BoxShrink.Core.Defs
import Submission.Work.CoreTopology.Basic
import Submission.Work.CoreTopology.isClosed_carrier
import Submission.Work.Topology.SphereSlicing.boxNorm_continuous

namespace Work.BoxShrink

open Set

/-- The cutting plane `{y | y (σ 2) = c (σ 2) + u}` is closed. -/
theorem isClosed_cutPlane (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    IsClosed (Work.BoxShrink.Core.cutPlane c σ u) := by
  have h : Work.BoxShrink.Core.cutPlane c σ u =
      {y : LeanEval.KnotTheory.PardonDistortion.R3 | y (σ 2) = c (σ 2) + u} := rfl
  rw [h]
  exact isClosed_eq (Work.Topology.SphereSlicing.continuous_coordR3 (σ 2)) continuous_const

/-- The closed sublevel `{y | boxNorm c σ y ≤ s}` of the box norm. -/
theorem isClosed_boxNorm_le (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (s : ℝ) :
    IsClosed {y : LeanEval.KnotTheory.PardonDistortion.R3 | Submission.boxNorm c σ y ≤ s} :=
  isClosed_le (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const

/-- If a point of the closure of the slice is in the *closed* box (`boxNorm ≤ s`) but not in the
open box (`boxNorm < s`), then it lies on the boundary sphere `boxNorm = s`, still in the plane. -/
theorem closure_sliceRegion_subset
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    closure (Work.BoxShrink.Core.sliceRegion P s c σ u) ⊆
      Work.BoxShrink.Core.sliceRegion P s c σ u ∪
        {y : LeanEval.KnotTheory.PardonDistortion.R3 |
          Submission.boxNorm c σ y = s ∧ y (σ 2) = c (σ 2) + u} := by
  intro y hy
  -- `y` is on the surface, since the carrier is closed and contains the slice.
  have hAc : y ∈ P.carrier :=
    ((Work.CoreTopology.isClosed_carrier P).closure_subset_iff).mpr
      (fun z hz => hz.1.1) hy
  -- `y` is in the cutting plane, since the plane is closed and contains the slice.
  have hplane : y (σ 2) = c (σ 2) + u :=
    (isClosed_cutPlane c σ u).closure_subset_iff.mpr (fun z hz => hz.2) hy
  -- `y` is in the closed box, since `{boxNorm ≤ s}` is closed and contains the slice.
  have hnorm : Submission.boxNorm c σ y ≤ s :=
    (isClosed_boxNorm_le c σ s).closure_subset_iff.mpr
      (fun z hz => le_of_lt ((Submission.mem_PBox_iff s c σ z).mp hz.1.2)) hy
  rcases lt_or_eq_of_le hnorm with hlt | heq
  · exact Or.inl ⟨⟨hAc, (Submission.mem_PBox_iff s c σ y).mpr hlt⟩, hplane⟩
  · exact Or.inr ⟨heq, hplane⟩

end Work.BoxShrink
