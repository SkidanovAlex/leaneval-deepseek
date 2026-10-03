import Mathlib
import Submission.Work.OROneRel.gaugeExtWindowDefs

namespace Work.OROneRel

/-- **Triviality of the walk of a window word, transported to an extension of the gauge.**

Let `Wt` be a gauge and `[lo,hi]` a level window such that every decorated letter of `wordOf (Wt k)`,
`lo ≤ k ≤ hi`, is a *tree edge* of the window (`coverEdge e ∈ winTree Wt c lo hi`), i.e. a window edge
whose loop class under `Wt` is trivial.  If `Wt'` is any other gauge agreeing with `Wt` on the window,
then for every `i` with `lo ≤ i ≤ hi` the word `wordOf (Wt i)` has trivial walk under `Wt'` as well.

The point is that the loop class `coverClassAt W c e` of an edge only reads `W` at the two endpoints
of `e`; for a window edge both endpoints lie in `[lo,hi]`, where `Wt'` and `Wt` agree, so the loop
classes coincide. -/
theorem gxTrivFrom_of_window {α : Type*} [DecidableEq α] {c : α → ℤ} {Wt Wt' : ℤ → FreeGroup α}
    {lo hi i : ℤ}
    (hagree : ∀ k : ℤ, lo ≤ k → k ≤ hi → Wt' k = Wt k)
    (htree : ∀ k : ℤ, lo ≤ k → k ≤ hi →
      ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (Wt k)),
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree Wt c lo hi)
    (hi1 : lo ≤ i) (hi2 : i ≤ hi) :
    Work.OROneRel.gxTrivFrom c Wt' 0 (Work.OROneRel.wordOf (Wt i)) := by
  intro p hp
  have hmem := htree i hi1 hi2 p hp
  rw [mem_winTree] at hmem
  obtain ⟨he, hcls⟩ := hmem
  rw [mem_winE] at he
  obtain ⟨h1, h2, h3, h4⟩ := he
  have heq : coverClassAt Wt' c (coverEdge p) = coverClassAt Wt c (coverEdge p) := by
    simp only [coverClassAt, gaugeMap_of]
    rw [hagree (coverEdge p).2 h1 h2,
      hagree ((coverEdge p).2 + c (coverEdge p).1) h3 h4]
  rw [heq, hcls]

end Work.OROneRel
