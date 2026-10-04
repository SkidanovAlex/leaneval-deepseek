import Mathlib
import Submission.Work.Diff.Dim2.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

/-- Every real inner product space of dimension `2` is isometric to `ℝ²`. -/
theorem exists_isometry_EuclideanTwo
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim2 : Module.finrank ℝ E = 2) :
    Nonempty (E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) :=
  -- An orthonormal basis of `E` indexed by `Fin (finrank ℝ E)`, reindexed along `hdim2` to
  -- `Fin 2`; coordinates in an orthonormal basis are a linear isometry onto `EuclideanSpace`.
  ⟨(stdOrthonormalBasis ℝ E).reindex (finCongr hdim2) |>.repr⟩

end Work.Diff.Dim2
