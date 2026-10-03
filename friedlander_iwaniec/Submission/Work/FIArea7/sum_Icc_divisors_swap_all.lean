import Mathlib
import Submission.Work.FIArea7.sum_Icc_divisors_swap_left

namespace Work.FIArea7

/-- Swapping the order of summation in a double sum over `n ∈ [1,N]` and *all* divisors
`a ∣ n`, reindexed by writing `n = a * m`.  Since `n ≤ N ≤ Y`, every divisor `a` of `n`
already satisfies `a ≤ Y`, so this is the `≤ Y`-filtered version
`sum_Icc_divisors_swap_left` with an empty filter. -/
theorem sum_Icc_divisors_swap_all {M : Type*} [AddCommMonoid M] (N Y : ℕ) (hNY : N ≤ Y)
    (G : ℕ → ℕ → M) :
    (∑ n ∈ Finset.Icc 1 N, ∑ a ∈ n.divisors, G a n)
      = ∑ a ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 (N / a), G a (a * m) := by
  have key : (∑ n ∈ Finset.Icc 1 N, ∑ a ∈ n.divisors, G a n)
      = ∑ n ∈ Finset.Icc 1 N, ∑ a ∈ n.divisors.filter (fun a => a ≤ Y), G a n := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_Icc] at hn
    rw [Finset.filter_true_of_mem]
    intro a ha
    rw [Nat.mem_divisors] at ha
    exact le_trans (Nat.le_of_dvd (by omega) ha.1) (le_trans hn.2 hNY)
  rw [key, sum_Icc_divisors_swap_left]

end Work.FIArea7
