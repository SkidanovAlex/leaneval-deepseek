import Mathlib
import Submission.Work.OROneRel.padDefs
import Submission.Work.OROneRel.toWord_padHom
import Submission.Work.OROneRel.expSum_none_padRel_padC
import Submission.Work.OROneRel.pad_isCyclicallyReduced

universe u

namespace Work.OROneRel

/-- The explicit shape of a padding block `(some a, s) :: (z^{|c a|} ++ [(some a, s)])`
(`pcr_padBlock_eq_true` / `pcr_padBlock_eq_false`, proved in
`Submission/Work/OROneRel/pad_isCyclicallyReduced.lean`) shows that when `c a ≠ 0`
the fresh letter `none` occurs in the block, with sign determined by `a` and the sign
of `c a`. -/
theorem mem_none_padBlock {α : Type u} (c : α → ℤ) (p : α × Bool) (hp : c p.1 ≠ 0) :
    ∃ b : Bool, (none, b) ∈ Work.OROneRel.padBlock c p := by
  obtain ⟨a, s⟩ := p
  have hne : (c a).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hp
  cases s
  · refine ⟨!(decide (0 < c a)), ?_⟩
    rw [pcr_padBlock_eq_false]
    exact List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_replicate.mpr ⟨hne, rfl⟩))
  · refine ⟨decide (0 < c a), ?_⟩
    rw [pcr_padBlock_eq_true]
    exact List.mem_cons_of_mem _
      (List.mem_append_left _ (List.mem_replicate.mpr ⟨hne, rfl⟩))

end Work.OROneRel
