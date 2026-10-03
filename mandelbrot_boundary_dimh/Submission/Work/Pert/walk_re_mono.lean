import Mathlib

namespace Work.Pert

/-- If a real walk `x` increases by at least `1/2` at every step below `k`, then it
grows at least linearly: `x j ≥ x i + (j - i)/2` for `i ≤ j ≤ k`. -/
lemma walk_re_mono {x : ℕ → ℝ} {k : ℕ} (hx : ∀ j < k, x j + 1 / 2 ≤ x (j + 1)) :
    ∀ i j, i ≤ j → j ≤ k → x i + ((j - i : ℕ) : ℝ) / 2 ≤ x j := by
  intro i j hij hjk
  -- Prove the statement by induction on the upper endpoint `n ≤ k`.
  have key : ∀ n ≤ k, ∀ i, i ≤ n → x i + ((n - i : ℕ) : ℝ) / 2 ≤ x n := by
    intro n
    induction n with
    | zero =>
      intro _ i hi
      interval_cases i
      simp
    | succ n ih =>
      intro hnk i hi
      rcases eq_or_lt_of_le hi with h | h
      · subst h; simp
      · have hin : i ≤ n := Nat.lt_succ_iff.mp h
        have h1 := ih (le_trans (Nat.le_succ n) hnk) i hin
        have h2 := hx n (Nat.lt_of_succ_le hnk)
        have hsub : ((n + 1 - i : ℕ) : ℝ) = ((n - i : ℕ) : ℝ) + 1 := by
          rw [Nat.succ_sub hin, Nat.cast_succ]
        rw [hsub]
        linarith
  exact key j hjk i hij

end Work.Pert
