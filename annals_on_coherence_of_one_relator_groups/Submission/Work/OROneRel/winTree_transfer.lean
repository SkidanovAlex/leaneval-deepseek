import Mathlib
import Submission.Work.OROneRel.reflectData

namespace Work.OROneRel

/-- **The tree hypothesis reflects.**  If for the weight `-c` and the window `[lo, hi]` every traversed edge of the walk of `Wt i` (for `i` in the window) is a tree edge, then for the weight `c`, the reflected gauge `j ↦ Wt (-j)` and the reflected window `[-hi, -lo]`, every traversed edge of the walk of `Wt (-i)` (for `i` in the reflected window) is a tree edge. -/
theorem winTree_transfer {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (h : ∀ i : ℤ, lo ≤ i → i ≤ hi → ∀ e ∈ Work.OROneRel.decor (fun a => -c a) 0
        (Work.OROneRel.wordOf (Wt i)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree Wt (fun a => -c a) lo hi) :
    ∀ i : ℤ, (-hi) ≤ i → i ≤ (-lo) → ∀ e ∈ Work.OROneRel.decor c 0
        (Work.OROneRel.wordOf (Wt (-i))),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree (fun j => Wt (-j)) c (-hi) (-lo) := by
  intro i hi_ge hi_le e he
  -- `-i` is in the original window `[lo, hi]`.
  have hjlo : lo ≤ -i := by omega
  have hjhi : -i ≤ hi := by omega
  -- The decorated walk of `Wt (-i)` at weight `-c` is the reflection of the one at weight `c`.
  have hmem : reflSym e ∈ decor (fun a => -c a) 0 (wordOf (Wt (-i))) := by
    rw [decor_neg_zero c (wordOf (Wt (-i)))]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have htree := h (-i) hjlo hjhi (reflSym e) hmem
  rw [mem_winTree] at htree
  rw [coverEdge_reflSym] at htree
  rw [mem_winTree]
  refine ⟨?_, ?_⟩
  · exact (mem_winE_reflEdge (c := c) (lo := lo) (hi := hi)).mp htree.1
  · rw [← coverClassAt_reflEdge_neg Wt c (coverEdge e)]
    exact htree.2

end Work.OROneRel
