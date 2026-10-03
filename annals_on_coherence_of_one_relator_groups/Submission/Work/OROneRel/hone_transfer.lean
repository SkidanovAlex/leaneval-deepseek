import Mathlib
import Submission.Work.OROneRel.reflectData

namespace Work.OROneRel

/-- **The window-minimality hypothesis reflects.**  If no non-zero translate of the walk of `u` fits in the window `[lo, hi]` of the weight `-c`, then no non-zero translate of the walk of `u` fits in the reflected window `[-hi, -lo]` of the weight `c`. -/
theorem hone_transfer {α : Type*} (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (h : ∀ k : ℤ, k ≠ 0 → ¬ (∀ e ∈ Work.OROneRel.decor (fun a => -c a) 0
        (Work.OROneRel.wordOf u),
        lo ≤ e.1.2 + k ∧ lo ≤ e.1.2 + (-c e.1.1) + k ∧ e.1.2 + k ≤ hi ∧
          e.1.2 + (-c e.1.1) + k ≤ hi)) :
    ∀ k : ℤ, k ≠ 0 → ¬ (∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
        (-hi) ≤ e.1.2 + k ∧ (-hi) ≤ e.1.2 + c e.1.1 + k ∧ e.1.2 + k ≤ (-lo) ∧
          e.1.2 + c e.1.1 + k ≤ (-lo)) := by
  -- The reflection `((x,i),b) ↦ ((x,-i),b)` identifies the decorated walk of `-c` at level `0`
  -- with the reflected decorated walk of `c` at level `0` (`decor_neg_zero`).  A non-zero shift
  -- `k` of the window `[lo,hi]` for `-c` therefore corresponds to the non-zero shift `-k` of the
  -- reflected window `[-hi,-lo]` for `c`, so the hypothesis transfers with `k ↦ -k`.
  intro k hk hcon
  refine h (-k) (neg_ne_zero.mpr hk) ?_
  intro e he
  rw [Work.OROneRel.decor_neg_zero] at he
  rw [List.mem_map] at he
  obtain ⟨p, hp, hpe⟩ := he
  have hc := hcon p hp
  rw [← hpe]
  simp only [Work.OROneRel.reflSym]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end Work.OROneRel
