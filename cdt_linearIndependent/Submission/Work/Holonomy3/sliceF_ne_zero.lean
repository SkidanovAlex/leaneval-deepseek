import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs

namespace Work.Holonomy3

/-- A non-zero finitely supported family `c` has a non-zero slice `sliceF c t` at some level `t`
occurring as a first coordinate in its support. -/
theorem sliceF_ne_zero {d : ℕ} (c : (Fin (d + 1) →₀ ℕ) →₀ ℂ) (hc : c ≠ 0) :
    ∃ t, t ∈ suppFst c ∧ sliceF c t ≠ 0 := by
  obtain ⟨m, hm⟩ := Finsupp.support_nonempty_iff.mpr hc
  refine ⟨m 0, mem_suppFst.mpr ⟨m, hm, rfl⟩, ?_⟩
  intro hzero
  have hmem : tailIdx m ∈ (sliceF c (m 0)).support := by
    rw [Finsupp.mem_support_iff, sliceF_apply, consIdx_tailIdx]
    exact Finsupp.mem_support_iff.mp hm
  rw [hzero] at hmem
  simp at hmem

end Work.Holonomy3
