import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Nat

namespace Commons.Algebra.BigOperators

variable {M : Type*} [CommMonoid M]

private lemma stepL (f : ℕ → M) (h : ℕ → ℕ → ℕ) (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), ∏ s ∈ Finset.range j, (f s) ^ (h j s))
      = (∏ j ∈ Finset.range n, ∏ s ∈ Finset.range j, (f s) ^ (h j s))
        * ∏ s ∈ Finset.range n, (f s) ^ (h n s) := by
  rw [Finset.prod_range_succ]

private lemma stepR (f : ℕ → M) (h : ℕ → ℕ → ℕ) (n : ℕ) :
    (∏ s ∈ Finset.range n, (f s) ^ (∑ j ∈ Finset.Icc (s + 1) n, h j s))
      = (∏ s ∈ Finset.range (n - 1), (f s) ^ (∑ j ∈ Finset.Icc (s + 1) (n - 1), h j s))
        * ∏ s ∈ Finset.range n, (f s) ^ (h n s) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Finset.prod_range_succ (fun s => (f s) ^ (∑ j ∈ Finset.Icc (s + 1) (m + 1), h j s)) m]
    rw [Finset.prod_range_succ (fun s => (f s) ^ (h (m + 1) s)) m]
    have key : ∀ s ∈ Finset.range m,
        (f s) ^ (∑ j ∈ Finset.Icc (s + 1) (m + 1), h j s)
          = (f s) ^ (∑ j ∈ Finset.Icc (s + 1) m, h j s) * (f s) ^ (h (m + 1) s) := by
      intro s hs
      rw [Finset.mem_range] at hs
      rw [← pow_add]
      congr 1
      exact Finset.sum_Icc_succ_top (by omega) (fun j => h j s)
    rw [Finset.prod_congr rfl key]
    rw [Finset.prod_mul_distrib]
    have hm : (f m) ^ (∑ j ∈ Finset.Icc (m + 1) (m + 1), h j m) = (f m) ^ (h (m + 1) m) := by
      rw [Finset.Icc_self, Finset.sum_singleton]
    rw [hm]
    ac_rfl

theorem prod_range_prod_range_pow_strict {M : Type*} [CommMonoid M] (f : ℕ → M) (h : ℕ → ℕ → ℕ)
    (n : ℕ) :
    (∏ j ∈ Finset.range n, ∏ s ∈ Finset.range j, (f s) ^ (h j s))
      = ∏ s ∈ Finset.range (n - 1),
          (f s) ^ (∑ j ∈ Finset.Icc (s + 1) (n - 1), h j s) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [stepL, stepR, ih]
    rw [show k + 1 - 1 = k from rfl]

end Commons.Algebra.BigOperators