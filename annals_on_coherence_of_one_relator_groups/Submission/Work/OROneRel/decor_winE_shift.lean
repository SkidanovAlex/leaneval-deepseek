import Mathlib
import Submission.Work.OROneRel.coverShift
import Submission.Work.OROneRel.winBasisDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The undirected edge of a shifted decorated letter: shifting the level of a decorated letter
shifts the second component of its edge by the same amount. -/
theorem coverEdge_coverShift (t : ℤ) (p : (α × ℤ) × Bool) :
    coverEdge (coverShift t p) = ((coverEdge p).1, (coverEdge p).2 + t) := rfl

/-- Shifting all level bounds of a window by `t` shifts the second component of an edge of the
window by `t`. -/
theorem mem_winE_shift {c : α → ℤ} {lo hi t : ℤ} {e : α × ℤ}
    (h : e ∈ winE c lo hi) : (e.1, e.2 + t) ∈ winE c (lo + t) (hi + t) := by
  rw [mem_winE] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **The window condition is invariant under a simultaneous level shift.**  If every edge of the
walk `decor c j M` lies in the window `[lo,hi]`, then every edge of the shifted walk
`decor c (j+t) M` lies in the shifted window `[lo+t,hi+t]`. -/
theorem decor_winE_shift {α : Type*} (c : α → ℤ) (j t lo hi : ℤ) (M : List (α × Bool))
    (h : ∀ e ∈ Work.OROneRel.decor c j M,
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c lo hi) :
    ∀ e ∈ Work.OROneRel.decor c (j + t) M,
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c (lo + t) (hi + t) := by
  intro e he
  rw [decor_shift_add c t j M] at he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  rw [coverEdge_coverShift]
  exact mem_winE_shift (h p hp)

end Work.OROneRel
