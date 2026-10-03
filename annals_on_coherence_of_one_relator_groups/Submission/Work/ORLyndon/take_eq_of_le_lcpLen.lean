import Mathlib
import Submission.Work.ORLyndon.fgdDefs

namespace Work.ORLyndon

/-- Any two lists agree on their first `m` entries as long as `m` is at most the length of their
longest common prefix. -/
theorem take_eq_of_le_lcpLen {β : Type*} [DecidableEq β] {W Z : List β} {m : ℕ}
    (h : m ≤ lcpLen W Z) : W.take m = Z.take m := by
  induction W generalizing Z m with
  | nil => simp at h; subst h; simp
  | cons a as ih =>
    cases Z with
    | nil => simp at h; subst h; simp
    | cons b bs =>
      simp only [lcpLen_cons_cons] at h
      by_cases hab : a = b
      · simp only [hab, if_true] at h
        cases m with
        | zero => simp
        | succ k =>
          simp only [List.take_succ_cons]
          have hk : k ≤ lcpLen as bs := by omega
          rw [hab, ih hk]
      · simp only [hab, if_false, Nat.le_zero] at h
        subst h
        simp

end Work.ORLyndon
