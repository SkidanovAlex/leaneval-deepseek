import Mathlib
import Submission.Work.FIChain.LamPlusBLayerDefs
import Submission.Work.FIChain.GpB_eq_VfB_add_oddLayers
import Submission.Work.FIChain.VfBFacts

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `TnB` recursion at an **even** index `n ≥ 2`: at an even index the layer condition
`TcondB` is vacuous, so the sum runs over all primes below `y`. -/
lemma TnB_eq_sum_primes_of_even (B : ℝ) (ν : ℕ → ℝ) (D y : ℝ) {n : ℕ} (h2 : 2 ≤ n)
    (he : Even n) :
    TnB B ν n D y = ∑ p ∈ Nat.primesBelow ⌈y⌉₊, ν p * TnB B ν (n - 1) (D / (p : ℝ)) (p : ℝ) := by
  have hn : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hn, TnB]
  rw [show n - 1 + 1 = n from hn.symm,
    Finset.filter_true_of_mem (fun p _ => TcondB_of_even B D p h2 he)]

/-- The `TnB` recursion at an **odd** index `n ≥ 3`: at an odd index `≥ 3` the layer condition
`TcondB` is exactly `p^{B+1} ≤ D`, so the sum runs over the primes `p < y` with `p^{B+1} ≤ D`. -/
lemma TnB_eq_sum_primes_of_odd (B : ℝ) (ν : ℕ → ℝ) (D y : ℝ) {n : ℕ} (h3 : 3 ≤ n)
    (ho : Odd n) :
    TnB B ν n D y
      = ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p : ℕ => (p : ℝ) ^ (B + 1) ≤ D),
          ν p * TnB B ν (n - 1) (D / (p : ℝ)) (p : ℝ) := by
  have hn : n = (n - 1) + 1 := by omega
  conv_lhs => rw [hn, TnB]
  rw [show n - 1 + 1 = n from hn.symm,
    Finset.filter_congr (fun p _ => TcondB_of_odd B D p (by omega) ho)]

theorem OddLayerSum_pair_recursion (B : ℝ) (ν : ℕ → ℝ) (M : ℕ) (hM : 2 ≤ M) (D y : ℝ) :
    (Work.FIChain.OddLayerSum B ν M D y
        = Work.FIChain.TnB B ν 1 D y
          + ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p : ℕ => (p : ℝ) ^ (B + 1) ≤ D),
              ν p * Work.FIChain.EvenPosLayerSum B ν (M - 1) (D / (p : ℝ)) (p : ℝ))
    ∧ (Work.FIChain.EvenPosLayerSum B ν M D y
        = ∑ p ∈ Nat.primesBelow ⌈y⌉₊,
            ν p * Work.FIChain.OddLayerSum B ν (M - 1) (D / (p : ℝ)) (p : ℝ)) := by
  constructor
  · -- Odd part: split off the `n = 1` layer, then apply the level-`(n+1)` recursion to every
    -- remaining odd layer `n ≥ 3` and exchange the two sums.
    have hset : (Finset.range M).filter (fun n : ℕ => Odd n)
        = insert 1 ((Finset.range M).filter (fun n : ℕ => Odd n ∧ 3 ≤ n)) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      constructor
      · rintro ⟨hnM, hodd⟩
        have hk := hodd
        obtain ⟨k, hk⟩ := hk
        rcases k with _ | k
        · left; omega
        · right; exact ⟨hnM, hodd, by omega⟩
      · rintro (rfl | ⟨hnM, hodd, h3⟩)
        · exact ⟨by omega, odd_one⟩
        · exact ⟨hnM, hodd⟩
    rw [OddLayerSum, hset, Finset.sum_insert (by simp)]
    congr 1
    rw [Finset.sum_congr rfl (fun n hn =>
      TnB_eq_sum_primes_of_odd B ν D y (Finset.mem_filter.mp hn).2.2
        (Finset.mem_filter.mp hn).2.1)]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => by rw [← Finset.mul_sum, sum_shift_odd])
  · -- Even part: every nonzero even layer `n ≥ 2` has a vacuous layer condition; apply the
    -- level-`(n+1)` recursion and exchange the two sums.
    have step1 : EvenPosLayerSum B ν M D y
        = ∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n ∧ n ≠ 0),
            ∑ p ∈ Nat.primesBelow ⌈y⌉₊, ν p * TnB B ν (n - 1) (D / (p : ℝ)) (p : ℝ) := by
      rw [EvenPosLayerSum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      obtain ⟨_, he, hne⟩ := Finset.mem_filter.mp hn
      have h2 : 2 ≤ n := by
        obtain ⟨k, hk⟩ := he
        omega
      exact TnB_eq_sum_primes_of_even B ν D y h2 he
    have step2 : (∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n ∧ n ≠ 0),
            ∑ p ∈ Nat.primesBelow ⌈y⌉₊, ν p * TnB B ν (n - 1) (D / (p : ℝ)) (p : ℝ))
        = ∑ p ∈ Nat.primesBelow ⌈y⌉₊,
            ∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n ∧ n ≠ 0),
              ν p * TnB B ν (n - 1) (D / (p : ℝ)) (p : ℝ) :=
      Finset.sum_comm
    have step3 : (∑ p ∈ Nat.primesBelow ⌈y⌉₊,
            ∑ n ∈ (Finset.range M).filter (fun n : ℕ => Even n ∧ n ≠ 0),
              ν p * TnB B ν (n - 1) (D / (p : ℝ)) (p : ℝ))
        = ∑ p ∈ Nat.primesBelow ⌈y⌉₊,
            ν p * OddLayerSum B ν (M - 1) (D / (p : ℝ)) (p : ℝ) := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [← Finset.mul_sum, sum_shift_even]
    exact step1.trans (step2.trans step3)

end

end Work.FIChain
