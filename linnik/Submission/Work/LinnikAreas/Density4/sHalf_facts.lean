import Mathlib
import Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
import Submission.Work.LinnikAreas.Density4.SelbergDefs

namespace Work.LinnikAreas.Density4

open Finset BigOperators
open scoped BigOperators

/-- Two basic facts about `σ_{-1/2}(r) = Σ_{d | r} 1/√d`:
(i) it dominates the Euler product `Π_{p | r}(1 + p^{-1/2})` (the squarefree divisors contribute
exactly that product), and (ii) for squarefree `r` the two agree.
Both are instances of `prod_primeFactors_one_add_eq_sum_divisors` applied to the multiplicative
function `d ↦ μ(d)²/√d`, which vanishes at prime powers `p^k`, `k ≥ 2`. -/
theorem sHalf_facts (r : ℕ) (hr : 1 ≤ r) :
    (∏ p ∈ r.primeFactors, (1 + (1:ℝ)/Real.sqrt p))
        ≤ ∑ d ∈ r.divisors, (1:ℝ)/Real.sqrt (d:ℝ) ∧
    (Squarefree r →
      (∑ d ∈ r.divisors, (1:ℝ)/Real.sqrt (d:ℝ))
        = ∏ p ∈ r.primeFactors, (1 + (1:ℝ)/Real.sqrt p)) := by
  classical
  have hr0 : r ≠ 0 := by omega
  have hf1 : (fun d : ℕ => if Squarefree d then (1:ℝ)/Real.sqrt (d:ℝ) else 0) 1 = 1 := by
    show (if Squarefree (1:ℕ) then (1:ℝ)/Real.sqrt ((1:ℕ):ℝ) else 0) = 1
    rw [if_pos squarefree_one, Nat.cast_one, Real.sqrt_one, div_one]
  have hfm : ∀ a b : ℕ, Nat.Coprime a b →
      (fun d : ℕ => if Squarefree d then (1:ℝ)/Real.sqrt (d:ℝ) else 0) (a*b)
        = (fun d : ℕ => if Squarefree d then (1:ℝ)/Real.sqrt (d:ℝ) else 0) a
          * (fun d : ℕ => if Squarefree d then (1:ℝ)/Real.sqrt (d:ℝ) else 0) b := by
    intro a b hab
    by_cases ha : Squarefree a
    · by_cases hb : Squarefree b
      · have hab' : Squarefree (a*b) := (Nat.squarefree_mul hab).mpr ⟨ha, hb⟩
        have hsq : Real.sqrt ((a:ℝ) * (b:ℝ)) = Real.sqrt (a:ℝ) * Real.sqrt (b:ℝ) :=
          Real.sqrt_mul (by positivity) _
        show (if Squarefree (a*b) then (1:ℝ)/Real.sqrt ((a*b:ℕ):ℝ) else 0)
            = (if Squarefree a then (1:ℝ)/Real.sqrt (a:ℝ) else 0)
              * (if Squarefree b then (1:ℝ)/Real.sqrt (b:ℝ) else 0)
        rw [if_pos hab', if_pos ha, if_pos hb, Nat.cast_mul, hsq, div_mul_div_comm, one_mul]
      · have hab' : ¬ Squarefree (a*b) := fun h => hb h.of_mul_right
        show (if Squarefree (a*b) then (1:ℝ)/Real.sqrt ((a*b:ℕ):ℝ) else 0)
            = (if Squarefree a then (1:ℝ)/Real.sqrt (a:ℝ) else 0)
              * (if Squarefree b then (1:ℝ)/Real.sqrt (b:ℝ) else 0)
        rw [if_neg hab', if_pos ha, if_neg hb, mul_zero]
    · have hab' : ¬ Squarefree (a*b) := fun h => ha h.of_mul_left
      show (if Squarefree (a*b) then (1:ℝ)/Real.sqrt ((a*b:ℕ):ℝ) else 0)
          = (if Squarefree a then (1:ℝ)/Real.sqrt (a:ℝ) else 0)
            * (if Squarefree b then (1:ℝ)/Real.sqrt (b:ℝ) else 0)
      rw [if_neg hab', if_neg ha, zero_mul]
  have hfs : ∀ p k : ℕ, p.Prime → 2 ≤ k →
      (fun d : ℕ => if Squarefree d then (1:ℝ)/Real.sqrt (d:ℝ) else 0) (p^k) = 0 := by
    intro p k hp hk
    show (if Squarefree (p^k) then (1:ℝ)/Real.sqrt ((p^k:ℕ):ℝ) else 0) = 0
    rw [if_neg]
    intro hsq
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp)
      (by simpa [pow_two] using pow_dvd_pow p hk)
  have hkey := Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
      (fun d : ℕ => if Squarefree d then (1:ℝ)/Real.sqrt (d:ℝ) else 0) r hr0 hf1 hfm hfs
  have hL : (∏ p ∈ r.primeFactors,
        (1 + (fun d : ℕ => if Squarefree d then (1:ℝ)/Real.sqrt (d:ℝ) else 0) p))
      = ∏ p ∈ r.primeFactors, (1 + (1:ℝ)/Real.sqrt (p:ℝ)) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    show (1 + (if Squarefree p then (1:ℝ)/Real.sqrt (p:ℝ) else 0))
        = (1 + (1:ℝ)/Real.sqrt (p:ℝ))
    rw [if_pos ((Nat.prime_iff.mp hpp).squarefree)]
  have hSsq : (∑ d ∈ r.divisors,
        (fun d : ℕ => if Squarefree d then (1:ℝ)/Real.sqrt (d:ℝ) else 0) d)
      = ∑ d ∈ r.divisors with Squarefree d, (1:ℝ)/Real.sqrt (d:ℝ) := by
    rw [Finset.sum_filter]
  have hSsq_le : (∑ d ∈ r.divisors with Squarefree d, (1:ℝ)/Real.sqrt (d:ℝ))
      ≤ ∑ d ∈ r.divisors, (1:ℝ)/Real.sqrt (d:ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset Squarefree r.divisors)
    intro d hd _
    exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
  constructor
  · rw [← hL, hkey, hSsq]
    exact hSsq_le
  · intro hsq
    have hfil : (∑ d ∈ r.divisors with Squarefree d, (1:ℝ)/Real.sqrt (d:ℝ))
        = ∑ d ∈ r.divisors, (1:ℝ)/Real.sqrt (d:ℝ) := by
      apply Finset.sum_congr
      · exact Finset.filter_true_of_mem
          (fun d hd => hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
      · intro d hd; rfl
    rw [← hL, hkey, hSsq, hfil]

end Work.LinnikAreas.Density4
