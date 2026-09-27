import Mathlib
import Submission.Work.PL.Shell.Basic

namespace Work.PL.Shell

/-- Swapping two adjacent entries of a list does not change the `toFinset` of the first `n`
entries, provided the cut does not fall strictly between the two swapped positions. -/
lemma take_toFinset_swap {α : Type*} [DecidableEq α] (a b : List α) (x y : α) {n : ℕ}
    (hn : n ≠ a.length + 1) :
    ((a ++ y :: x :: b).take n).toFinset = ((a ++ x :: y :: b).take n).toFinset := by
  rcases lt_trichotomy n (a.length + 1) with h | h | h
  · have hnle : n ≤ a.length := by omega
    rw [List.take_append_of_le_length hnle, List.take_append_of_le_length hnle]
  · exact absurd h hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = a.length + (m + 2) := ⟨n - a.length - 2, by omega⟩
    rw [List.take_append, List.take_append, Nat.add_sub_cancel_left]
    simp only [List.take_succ_cons, List.toFinset_cons, List.toFinset_append]
    rw [Finset.insert_comm]

/-- Swapping two adjacent elements in the middle of a list preserves the permutation. -/
lemma perm_swap_append_cons {α : Type*} (a b : List α) (x y : α) :
    (a ++ y :: x :: b).Perm (a ++ x :: y :: b) :=
  (List.Perm.swap x y b).append_left a

theorem swap_adjacent {α : Type*} [DecidableEq α] {l : List α} {s : ℕ} (hs : s + 1 < l.length) :
    (l.take s ++ [l[s + 1]'hs, l[s]'(Nat.lt_of_succ_lt hs)] ++ l.drop (s + 2)).Perm l ∧
    (∀ j, j ≠ s → Work.PL.Shell.prefAt
        (l.take s ++ [l[s + 1]'hs, l[s]'(Nat.lt_of_succ_lt hs)] ++ l.drop (s + 2)) j
      = Work.PL.Shell.prefAt l j) := by
  set a := l.take s with ha
  set y := l[s+1]'hs with hy
  set x := l[s]'(Nat.lt_of_succ_lt hs) with hx
  set b := l.drop (s + 2) with hb
  have hmL : a ++ [y, x] ++ b = a ++ y :: x :: b := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have ha_len : a.length = s := by rw [ha, List.length_take]; omega
  have hl : l = a ++ x :: y :: b := by
    have h1 : l.drop s = l[s]'(Nat.lt_of_succ_lt hs) :: l.drop (s + 1) :=
      List.drop_eq_getElem_cons (Nat.lt_of_succ_lt hs)
    have h2 : l.drop (s + 1) = l[s+1]'hs :: l.drop (s + 2) := List.drop_eq_getElem_cons hs
    calc l = l.take s ++ l.drop s := (List.take_append_drop s l).symm
      _ = l.take s ++ (l[s]'(Nat.lt_of_succ_lt hs) :: l.drop (s + 1)) := by rw [h1]
      _ = l.take s ++ (l[s]'(Nat.lt_of_succ_lt hs) :: l[s+1]'hs :: l.drop (s + 2)) := by rw [h2]
      _ = a ++ x :: y :: b := by rw [← ha, ← hx, ← hy, ← hb]
  constructor
  · rw [hmL, hl]
    exact perm_swap_append_cons a b x y
  · intro j hj
    rw [hmL, hl]
    show ((a ++ y :: x :: b).take (j + 1)).toFinset = ((a ++ x :: y :: b).take (j + 1)).toFinset
    exact take_toFinset_swap a b x y (by intro h; exact hj (by omega))

end Work.PL.Shell
