import Mathlib

namespace Work.PL.Shell

/-- If a sequence increases somewhere between `t` and `i`, then it increases at
some consecutive pair inside the interval: there is `s` with `t ≤ s < i` and
`a s < a (s + 1)`. -/
theorem exists_ascent {a : ℕ → ℕ} {t i : ℕ} (hti : t < i) (h : a t < a i) :
    ∃ s, t ≤ s ∧ s < i ∧ a s < a (s + 1) := by
  by_contra hcon
  -- If there is no ascent, the sequence is non-increasing on the whole interval.
  have hmono : ∀ s, t ≤ s → s < i → a (s + 1) ≤ a s := by
    intro s hts hsi
    by_contra hlt
    exact hcon ⟨s, hts, hsi, Nat.lt_of_not_le hlt⟩
  -- Hence it never exceeds its value at `t` on `[t, i]`.
  have key : a i ≤ a t := by
    have hkey : ∀ n, t ≤ n → n ≤ i → a n ≤ a t := by
      intro n htn
      induction n, htn using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ k hk ih =>
        intro hki
        have hk_i : k ≤ i := Nat.le_trans (Nat.le_succ k) hki
        exact Nat.le_trans (hmono k hk (Nat.lt_of_succ_le hki)) (ih hk_i)
    exact hkey i (Nat.le_of_lt hti) le_rfl
  exact absurd h (not_lt.mpr key)

end Work.PL.Shell
