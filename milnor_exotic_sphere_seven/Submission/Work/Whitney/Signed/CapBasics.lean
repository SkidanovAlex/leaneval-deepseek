import Mathlib
import Submission.Work.Whitney.capCycle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-!
# The two caps in `tcmF`-coordinates

`Work.Whitney.capX` (`rankOne_cup_model.lean`) and `Work.Whitney.lowerCapX` (`lowerCap.lean`) are
the upper and lower caps `Y × Dᵏ → tcmX Y k 1 = Y × (ℝᵏ × ℝ)`.  Through the coordinate
identification `Work.Whitney.tcmF` they become the ordinary upper and lower caps
`Work.Thom.capMap k` and `Work.Thom.lowerCapMap k` into `Y × Sᵏ ⊆ Y × ℝᵏ⁺¹`.

This file records that dictionary, together with the two point-level facts used by the cap-based
cycle of the rank-one model product formula: the upper cap lands in the sphere `{|w| = 1}`, the
lower cap lands in the lower band `mLower k = {|w| = 1, last ≤ 1/2}`.
-/

namespace Work.Whitney

open Work.Thom
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

noncomputable section

/-- **The upper cap in `tcmF`-coordinates**: `tcmF ∘ capX` is the graph of the upper hemisphere. -/
theorem tcmF_capX_apply (Y : Type) [TopologicalSpace Y] (k : ℕ) (q : Y × MBall k) :
    tcmF Y k 1 (capX Y k q) = (q.1, capMap k q.2.1) := by
  simp only [capX_apply, tcmF, ContinuousMap.coe_mk, ContinuousLinearEquiv.apply_symm_apply]

/-- **The lower cap in `tcmF`-coordinates**: `tcmF ∘ lowerCapX` is the graph of the lower
hemisphere. -/
theorem tcmF_lowerCapX_apply (Y : Type) [TopologicalSpace Y] (k : ℕ) (q : Y × MBall k) :
    tcmF Y k 1 (lowerCapX Y k q) = (q.1, lowerCapMap k q.2.1) := by
  simp only [lowerCapX_apply, tcmF, ContinuousMap.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The upper cap lands in the sphere bundle of rank `k+1`. -/
theorem tcmF_capX_mem_Sph (Y : Type) [TopologicalSpace Y] (k : ℕ) (q : Y × MBall k) :
    tcmF Y k 1 (capX Y k q) ∈ Sph Y (k + 1) := by
  rw [tcmF_capX_apply]
  exact capMap_mem_mSph k q.2.2

/-- The lower cap lands in the lower band `mLower k` of the sphere of rank `k+1`. -/
theorem tcmF_lowerCapX_mem_mLower (Y : Type) [TopologicalSpace Y] (k : ℕ) (q : Y × MBall k) :
    (tcmF Y k 1 (lowerCapX Y k q)).2 ∈ mLower k := by
  rw [tcmF_lowerCapX_apply]
  refine ⟨lowerCapMap_mem_mSph k q.2.2, ?_⟩
  rw [lowerCapMap_last]
  have h : 0 ≤ Real.sqrt (1 - ‖(q.2 : EuclideanSpace ℝ (Fin k))‖ ^ 2) := Real.sqrt_nonneg _
  linarith

end

end Work.Whitney
