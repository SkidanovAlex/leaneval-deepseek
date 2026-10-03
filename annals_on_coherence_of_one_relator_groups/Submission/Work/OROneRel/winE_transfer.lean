import Mathlib
import Submission.Work.OROneRel.reflectData

namespace Work.OROneRel

/-- **The window hypothesis reflects.**  If every traversed edge of the walk of `u` lies in the window `[lo, hi]` of the weight `-c`, then every traversed edge of the walk of `u` lies in the window `[-hi, -lo]` of the weight `c`. -/
theorem winE_transfer {α : Type*} (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (h : ∀ e ∈ Work.OROneRel.decor (fun a => -c a) 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (fun a => -c a) lo hi) :
    ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c (-hi) (-lo) := by
  intro e he
  -- The reflected symbol `reflSym e` is a traversed symbol of the walk for the weight `-c`:
  -- the decorated walk of `-c` is the reflection of the decorated walk of `c`.
  have hmem : reflSym e ∈ decor (fun a => -c a) 0 (wordOf u) := by
    rw [decor_neg_zero c (wordOf u)]
    exact List.mem_map.2 ⟨e, he, rfl⟩
  -- The hypothesis applied to the reflected symbol puts the reflected edge in the window `[lo,hi]`.
  have h' : reflEdge (coverEdge e) ∈ winE (fun a => -c a) lo hi := by
    have := h (reflSym e) hmem
    rwa [coverEdge_reflSym] at this
  -- Reflecting back the edge turns the window `[lo,hi]` of `-c` into the window `[-hi,-lo]` of `c`.
  exact mem_winE_reflEdge.mp h'

end Work.OROneRel
