import Mathlib.Data.Finset.Card

namespace Commons.Data.Finset

/-- If a subset of `{0, ..., q-1}` with `q ≥ 8` has at least `q - 3` elements,
then it contains two consecutive natural numbers `j, j+1 < q`. -/
theorem two_consecutive_of_large {q : ℕ} (hq : 8 ≤ q) (s : Finset ℕ)
    (hs : s ⊆ Finset.range q) (hcard : q - 3 ≤ s.card) :
    ∃ j : ℕ, j + 1 < q ∧ j ∈ s ∧ j + 1 ∈ s := by
  by_contra h
  -- No pair of consecutive elements can both lie in `s` (the bound `j+1 < q` is then automatic).
  have hno : ∀ j : ℕ, j ∈ s → j + 1 ∉ s := by
    intro j hjs hj1s
    have hj1q : j + 1 < q := Finset.mem_range.mp (hs hj1s)
    exact h ⟨j, hj1q, hjs, hj1s⟩
  let t : Finset ℕ := s.image (fun x => x + 1)
  -- `s` and its translate `t = s + 1` are disjoint and live inside `{0, ..., q}`.
  have hsub : s ∪ t ⊆ Finset.range (q + 1) := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hxs | hxt
    · exact Finset.mem_range.mpr
        (Nat.lt_trans (Finset.mem_range.mp (hs hxs)) (Nat.lt_succ_self q))
    · rcases Finset.mem_image.mp hxt with ⟨y, hy, hxy⟩
      apply Finset.mem_range.mpr
      rw [← hxy]
      exact Nat.succ_lt_succ (Finset.mem_range.mp (hs hy))
  have hdisj : Disjoint s t := by
    rw [Finset.disjoint_left]
    intro x hxs hxt
    rcases Finset.mem_image.mp hxt with ⟨y, hy, hxy⟩
    have hy1s : y + 1 ∈ s := by
      rw [hxy]
      exact hxs
    exact hno y hy hy1s
  have ht : t.card = s.card := by
    exact Finset.card_image_of_injective s Nat.succ_injective
  have hsum : s.card + t.card ≤ q + 1 := by
    calc
      s.card + t.card = (s ∪ t).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Finset.range (q + 1)).card := Finset.card_le_card hsub
      _ = q + 1 := by simp
  have h2 : 2 * s.card ≤ q + 1 := by
    rw [ht] at hsum
    omega
  omega

end Commons.Data.Finset