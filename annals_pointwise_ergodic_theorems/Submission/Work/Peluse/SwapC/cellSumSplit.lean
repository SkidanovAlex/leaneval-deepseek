import Mathlib
import Submission.Work.Peluse.SwapC.cprocNodup

namespace Work.Peluse.SwapC

/-- The cell sum is additive over concatenation of leaf lists. -/
lemma cellSum_append {s : ℕ} (A B : List (CLeaf s)) :
    cellSum (A ++ B) = cellSum A + cellSum B := by
  simp [cellSum, List.map_append, List.sum_append]

/-- Splitting a leaf of depth `< s` into its two children preserves the cell sum: the two children
have depth `dep + 1`, and `2 ^ (s - (dep + 1)) + 2 ^ (s - (dep + 1)) = 2 ^ (s - dep)`. -/
lemma cellSum_children {s : ℕ} {m : CLeaf s} (h : m.dep < s) :
    cellSum (m.children h) = 2 ^ (s - m.dep) := by
  rw [CLeaf.children]
  have h1 : s - m.dep = (s - (m.dep + 1)) + 1 := by omega
  simp [cellSum, h1, pow_succ]
  ring

/-- Replacing a leaf `m` by its two children does not change the cell sum of the list. -/
theorem cellSumSplit {s : ℕ} {P Q : List (Work.Peluse.SwapC.CLeaf s)} {m : Work.Peluse.SwapC.CLeaf s}
    (h : m.dep < s) :
    Work.Peluse.SwapC.cellSum (P ++ m.children h ++ Q) = Work.Peluse.SwapC.cellSum (P ++ m :: Q) := by
  rw [List.append_assoc, cellSum_append, cellSum_append, cellSum_children h, cellSum_append]
  simp [cellSum]

end Work.Peluse.SwapC
