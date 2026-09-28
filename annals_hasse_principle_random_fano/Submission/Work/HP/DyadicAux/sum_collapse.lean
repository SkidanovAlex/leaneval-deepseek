import Mathlib

/-!
# Collapsing a triangular double sum into a diagonal sum

This file proves the elementary combinatorial identity which reindexes a
double sum over the triangle `{(a, b) : a + b < n}` by the value of `a + b`.

For any additive commutative monoid and any `f : ℕ → ℕ → α`,

  `∑ a < n, ∑ b < n - a, f a b = ∑ s < n, ∑ a < s + 1, f a (s - a)`.

The proof is a straightforward induction on `n`; the point is that going from
`n` to `n + 1` adds exactly the boundary term `f n 0` to both sides together
with the sum of the new antidiagonal `f a (n - a)`.

This is then used to collapse the outer rectangle `range (M+1) × range (M+1)`
of a function vanishing above the diagonal `a + b = M`.
-/

namespace Work.HP.DyadicAux

/-- Reindex a double sum over the triangle `a + b < n` by the antidiagonals
`a + b = s`. -/
lemma sum_range_sub_sum_range_succ {α : Type*} [AddCommMonoid α] (f : ℕ → ℕ → α) (n : ℕ) :
    (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range (n - a), f a b)
      = ∑ s ∈ Finset.range n, ∑ a ∈ Finset.range (s + 1), f a (s - a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a), f a b)
        = (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range (n - a), f a b)
          + (∑ a ∈ Finset.range n, f a (n - a)) + f n 0 := by
      rw [Finset.sum_range_succ]
      have key : (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range (n + 1 - a), f a b)
          = (∑ a ∈ Finset.range n, ∑ b ∈ Finset.range (n - a), f a b)
            + ∑ a ∈ Finset.range n, f a (n - a) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        have hlt : a < n := Finset.mem_range.mp ha
        have hidx : n + 1 - a = (n - a) + 1 := by omega
        rw [hidx, Finset.sum_range_succ]
      rw [key]
      have hn : n + 1 - n = 1 := by omega
      rw [hn]
      simp
    have hB : (∑ s ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (s + 1), f a (s - a))
        = (∑ s ∈ Finset.range n, ∑ a ∈ Finset.range (s + 1), f a (s - a))
          + (∑ a ∈ Finset.range n, f a (n - a)) + f n 0 := by
      rw [Finset.sum_range_succ]
      have h2 : (∑ a ∈ Finset.range (n + 1), f a (n - a))
          = (∑ a ∈ Finset.range n, f a (n - a)) + f n (n - n) :=
        Finset.sum_range_succ (fun a => f a (n - a)) n
      rw [h2, Nat.sub_self, add_assoc]
    rw [hA, hB, ih]

/-- Collapse the rectangular double sum `∑ a ≤ M, ∑ b ≤ M` of a function that
vanishes whenever `M < a + b` into the diagonal sum
`∑ s ≤ M, ∑ a ≤ s, h a (s - a)`. -/
theorem sum_collapse (h : ℕ → ℕ → ℝ) (M : ℕ) (hzero : ∀ a b, M < a + b → h a b = 0) :
    (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1), h a b)
      = ∑ s ∈ Finset.range (M + 1), ∑ a ∈ Finset.range (s + 1), h a (s - a) := by
  rw [← sum_range_sub_sum_range_succ h (M + 1)]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a < M + 1 := Finset.mem_range.mp ha
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro b hb hnb
    simp only [Finset.mem_range] at hb hnb
    apply hzero
    omega

end Work.HP.DyadicAux
