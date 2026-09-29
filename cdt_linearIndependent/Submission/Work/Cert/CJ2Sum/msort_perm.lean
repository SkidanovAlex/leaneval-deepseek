/-
`msort f l` is a merge sort (with fuel `f`) of the list `l` of `(value, weight)` pairs; in
particular it is a *rearrangement* of `l`, which is what the certificate needs: the sorted order
only affects the order of summation of `sortedSum`, not the multiset of pairs.

Both `merge` and `msort` are the data-free copies defined in `Submission.Work.Cert.CJ2.Gen`.
-/
import Mathlib
import Submission.Work.Cert.CJ2.Gen

namespace Work.Cert.CJ2Sum

open Work.Cert.CJ2

/-- `merge` of two lists is a rearrangement of their concatenation.  Note that this is true for
*every* fuel: when the fuel runs out the definition falls back to `xs ++ ys`, which is the
concatenation itself. -/
theorem merge_perm (f : ℕ) (xs ys : List (ℤ × ℤ)) : (merge f xs ys).Perm (xs ++ ys) := by
  induction f generalizing xs ys with
  | zero => simp [merge]
  | succ f ih =>
    cases xs with
    | nil => simp [merge]
    | cons x xs =>
      cases ys with
      | nil => simp [merge]
      | cons y ys =>
        simp only [merge]
        split
        · exact (ih xs (y :: ys)).cons x
        · refine ((ih (x :: xs) ys).cons y).trans ?_
          have h := (List.perm_append_comm (l₁ := [y]) (l₂ := x :: xs)).append_right ys
          simpa using h

/-- Merge sort rearranges its input (whatever the fuel). -/
theorem msort_perm_aux (f : ℕ) (l : List (ℤ × ℤ)) : (msort f l).Perm l := by
  induction f generalizing l with
  | zero => exact List.Perm.refl l
  | succ f ih =>
    cases l with
    | nil => simp [msort]
    | cons x t =>
      cases t with
      | nil => simp [msort]
      | cons y u =>
        simp only [msort]
        exact ((merge_perm _ _ _).trans ((ih _).append (ih _))).trans
          (by rw [List.take_append_drop])

theorem msort_perm (f : ℕ) (l : List (ℤ × ℤ)) : l.Perm (Work.Cert.CJ2.msort f l) :=
  (msort_perm_aux f l).symm

end Work.Cert.CJ2Sum
