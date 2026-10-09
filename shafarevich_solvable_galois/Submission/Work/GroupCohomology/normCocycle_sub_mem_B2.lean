import Mathlib
import Submission.Work.GroupCohomology.Extension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- The cochain `c - normCocycle c`, which sends `(q, r)` to `c (q, 1)`, is a coboundary when
`c` is a `2`-cocycle: indeed `c (q, 1) = q • c (1, 1)`, so it is `d¹` of the constant function
`q ↦ c (1, 1)`. -/
theorem normCocycle_sub_mem_B2 {Q : Type*} {A : Type*} [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] (c : Q × Q → A) (hc : c ∈ Work.GroupCohomology.Z2 Q A) :
    c - Work.GroupCohomology.normCocycle Q A c ∈ Work.GroupCohomology.B2 Q A := by
  rw [mem_B2_iff Q A]
  refine ⟨fun _ => c (1, 1), ?_⟩
  funext p
  obtain ⟨q, r⟩ := p
  simp only [d1_apply, normCocycle_apply, Pi.sub_apply]
  rw [Z2.map_one_snd Q A hc q]
  abel

end Work.GroupCohomology
