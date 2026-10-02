import Mathlib
import Submission.Work.Thom.manifoldP1
import Submission.Work.Thom.chernClass_eq_zero_of_lt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

/-- **`p₁(TM)` vanishes in ranks `≤ 1`.**  The first Pontryagin class is defined as
`p₁(TM) = - c₂(TM ⊗_ℝ ℂ)`, and the second Chern class of a complex bundle of rank `m` vanishes as
soon as `m < 2` (`Work.Thom.chernClass_eq_zero_of_lt`).  Hence for a manifold whose model space has
dimension at most one, `p₁(TM) = 0`. -/
theorem p1Tangent_eq_zero_of_finrank_le_one {E H : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M]
    [FiniteDimensional ℝ E] (h : Module.finrank ℝ E ≤ 1) : Work.Thom.p1Tangent' I M = 0 := by
  rw [p1Tangent'_def]
  have hlt : Module.finrank ℝ E < 2 := by omega
  rw [chernClass_eq_zero_of_lt (complexifiedTangentBundleFinite I M) hlt]
  exact neg_zero

end Work.Thom
