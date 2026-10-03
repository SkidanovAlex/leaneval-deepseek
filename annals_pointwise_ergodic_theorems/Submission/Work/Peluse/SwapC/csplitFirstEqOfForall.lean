import Mathlib
import Submission.Work.Peluse.SwapC.cprocNodup

namespace Work.Peluse.SwapC

/-- `csplitFirst` given a head that is not splittable: it leaves the head and recurses. -/
private lemma csplitFirst_cons_of_not_lt {s : ℕ} {a : CLeaf s} {rest : List (CLeaf s)}
    (ha : ¬ a.dep < s) : csplitFirst (a :: rest) = a :: csplitFirst rest := by
  rw [csplitFirst, dif_neg ha]

/-- `csplitFirst` given a splittable head: it replaces the head by its two children. -/
private lemma csplitFirst_cons_of_lt {s : ℕ} {m : CLeaf s} {Q : List (CLeaf s)}
    (hm : m.dep < s) : csplitFirst (m :: Q) = m.children hm ++ Q := by
  rw [csplitFirst, dif_pos hm]

theorem csplitFirstEqOfForall {s : ℕ} {P Q : List (Work.Peluse.SwapC.CLeaf s)}
    {m : Work.Peluse.SwapC.CLeaf s} (hP : ∀ a ∈ P, ¬ a.dep < s) (hm : m.dep < s) :
    Work.Peluse.SwapC.csplitFirst (P ++ m :: Q) = P ++ m.children hm ++ Q := by
  induction P with
  | nil => simpa using csplitFirst_cons_of_lt (Q := Q) hm
  | cons a P ih =>
    have ha : ¬ a.dep < s := hP a (by simp)
    have hP' : ∀ b ∈ P, ¬ b.dep < s := fun b hb => hP b (by simp [hb])
    rw [List.cons_append, csplitFirst_cons_of_not_lt ha, ih hP']
    simp [List.cons_append]

end Work.Peluse.SwapC
