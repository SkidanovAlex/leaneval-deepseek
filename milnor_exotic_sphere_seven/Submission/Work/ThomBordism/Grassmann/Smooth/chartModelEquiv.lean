import Mathlib
import Submission.Work.ThomBordism.Grassmann.Frame

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Grassmann.Smooth

open Work.ThomBordism.Grassmann

/-- The space of continuous linear maps `ℝ^k → ℝ^m` is linearly isometric to the Euclidean space
`ℝ^{km}`: both are finite-dimensional real normed spaces of dimension `k * m`. -/
theorem chartModelEquiv (k m : ℕ) :
    Nonempty ((Amb k →L[ℝ] Amb m) ≃L[ℝ] EuclideanSpace ℝ (Fin (k * m))) := by
  refine ⟨ContinuousLinearEquiv.ofFinrankEq ?_⟩
  rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Amb k) (F' := Amb m)).finrank_eq]
  rw [Module.finrank_linearMap]
  simp

end Work.ThomBordism.Grassmann.Smooth
