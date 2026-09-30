import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Discrete Abel summation (summation by parts) over `Ioc N M`

This file proves `Work.BMF.ioc_abel_identity`: for complex sequences `a`, `w` and a partial-sum
sequence `A` of `a` starting at `N` (`A N = 0` and `A (k+1) = A k + a (k+1)` for `k ≥ N`),

`∑_{n ∈ Ioc N M} w n * a n = w M * A M + ∑_{n ∈ Ioc N (M-1)} (w n - w (n+1)) * A n`,

for `N < M`.  This is the standard "Abel summation"/partial-summation identity in the form
used when the weight `w` is a smooth/short-interval weight and the partial sums `A` are the
object being bounded.

Route: strong-enough induction on `M` (peeling the top term `n = M` from both sums) together
with the elementary observation that the `N`-term of the difference sum drops out because
`A N = 0`.
-/

namespace Work.BMF

/-- Splitting off the top element of a sum over `Ioc a m`, in the form where the top term
appears as `f m` (rather than `f ((m-1)+1)`). -/
lemma sum_Ioc_pred_succ_top {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a m : ℕ} (h : a < m) :
    ∑ n ∈ Finset.Ioc a m, f n = (∑ n ∈ Finset.Ioc a (m - 1), f n) + f m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  rw [Finset.sum_Ioc_succ_top (show a ≤ k by omega), Nat.succ_sub_one]

/-- **Discrete Abel summation on `Ioc N M`.**  If `A` is the partial-sum sequence of `a`
starting at `N` (`A N = 0`, `A (k+1) = A k + a (k+1)` for `k ≥ N`) then, for `N < M`,
`∑_{n ∈ Ioc N M} w n * a n = w M * A M + ∑_{n ∈ Ioc N (M-1)} (w n - w (n+1)) * A n`. -/
theorem ioc_abel_identity (a w : ℕ → ℂ) (A : ℕ → ℂ) (N M : ℕ)
    (hA0 : A N = 0)
    (hstep : ∀ k, N ≤ k → A (k + 1) = A k + a (k + 1))
    (hNM : N < M) :
    ∑ n ∈ Finset.Ioc N M, w n * a n
      = w M * A M + ∑ n ∈ Finset.Ioc N (M - 1), (w n - w (n + 1)) * A n := by
  have key : ∀ M, N < M →
      (∑ n ∈ Finset.Ioc N M, w n * a n
        = w M * A M + ∑ n ∈ Finset.Ioc N (M - 1), (w n - w (n + 1)) * A n) := by
    intro M
    induction M with
    | zero => intro h; exact absurd h (Nat.not_lt_zero N)
    | succ m ih =>
      intro hm
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with h | h
      · -- induction step: peel the term `n = m + 1` from the left sum and the term `n = m`
        -- from the right sum
        rw [Finset.sum_Ioc_succ_top (show N ≤ m by omega) (f := fun n => w n * a n)]
        rw [ih h]
        rw [show m + 1 - 1 = m from Nat.add_sub_cancel m 1]
        rw [sum_Ioc_pred_succ_top (f := fun n => (w n - w (n + 1)) * A n) (show N < m by omega)]
        rw [hstep m (show N ≤ m by omega)]
        ring
      · -- base case: `m = N`, where `A (N+1) = a (N+1)` because `A N = 0`
        rw [← h]
        rw [Finset.sum_Ioc_succ_top (le_refl N) (f := fun n => w n * a n)]
        rw [Finset.Ioc_self, Finset.sum_empty, zero_add]
        rw [show N + 1 - 1 = N from Nat.add_sub_cancel N 1, Finset.Ioc_self, Finset.sum_empty,
          add_zero]
        rw [hstep N le_rfl, hA0, zero_add]
  exact key M hNM

end Work.BMF
