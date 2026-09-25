import Mathlib

namespace Work.LT

/-- Binomial coefficients are nondecreasing in the lower index as long as that index stays
below `n / 2`. This is the integrated form of `Nat.choose_le_succ_of_lt_half_left`. -/
private lemma choose_mono_of_le_half :
    ∀ {n r s : ℕ}, r ≤ s → s ≤ n / 2 → n.choose r ≤ n.choose s
  | n, r, 0, hrs, _ => by
      have h : r = 0 := Nat.eq_zero_of_le_zero hrs
      subst h
      exact le_rfl
  | n, r, s + 1, hrs, hs => by
      rcases Nat.eq_or_lt_of_le hrs with h | h
      · subst h; exact le_rfl
      · exact (choose_mono_of_le_half (Nat.le_of_lt_succ h)
            (Nat.le_trans (Nat.le_succ s) hs)).trans
          (Nat.choose_le_succ_of_lt_half_left (Nat.lt_of_succ_le hs))

/-- Binomial coefficients `(n choose k)` are nondecreasing in `k` up to `k = w` when `2w ≤ n`. -/
theorem binom_mono_second (n w k : ℕ) (hk : k ≤ w) (hw : 2 * w ≤ n) :
    n.choose k ≤ n.choose w :=
  choose_mono_of_le_half hk (by omega)

end Work.LT
