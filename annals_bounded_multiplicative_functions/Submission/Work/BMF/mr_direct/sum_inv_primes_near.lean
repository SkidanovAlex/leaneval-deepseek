import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.sum_inv_primes_le
import Submission.Work.BMF.mr_direct.sum_inv_primes_near_arith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- For nonnegative `f`, the sum over a union is at most the sum of the two sums. -/
private lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have hun : s ∪ t = s ∪ (t \ s) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  rw [hun, Finset.sum_union Finset.disjoint_sdiff]
  have h2 : ∑ x ∈ t \ s, f x ≤ ∑ x ∈ t, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i _ _ => hf i)
  linarith

/-- The sum of `1/p` over the primes of the two short multiplicative intervals
`[A e^{-1/K}, A]` and `[A, A e^{1/K}]` is at most `16 (1/K + 1/A)`.

Both pieces carry a *crude* counting bound: on `[l, u]` each prime `p ≥ l` contributes at most
`1/l` and there are at most `u + 1 - l` primes, so the sum is at most `(u + 1 - l)/l`; for the
lower piece (`l = L = A e^{-1/K}`, `u = A`) this is `e^{1/K} - 1 + e^{1/K}/A`, and for the upper
piece (`l = A`, `u = A e^{1/K}`) it is `e^{1/K} - 1 + 1/A`. Adding, the total is at most
`2(e^{1/K} - 1) + (e^{1/K} + 1)/A ≤ 4/K + 4/A ≤ 16(1/K + 1/A)`, using
`|e^{1/K} - 1| ≤ 2/K` (`Real.abs_exp_sub_one_le`, valid since `K ≥ 1`) and `e^{1/K} < 3`. -/
lemma sum_inv_primes_near (A K : ℝ) (hA : 2 ≤ A) (hK : 1 ≤ K) :
    ∑ p ∈ (Work.BMF.primesIn (A * Real.exp (-(1 / K))) A) ∪
            (Work.BMF.primesIn A (A * Real.exp (1 / K))),
        (1 : ℝ) / (p : ℝ) ≤ 16 * (1 / K + 1 / A) := by
  set L := A * Real.exp (-(1 / K)) with hL
  set U := A * Real.exp (1 / K) with hU
  have hApos : 0 < A := by linarith
  have hLpos : 0 < L := by rw [hL]; positivity
  have hLA : L ≤ A := by
    rw [hL]
    have he : Real.exp (-(1 / K)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0:ℝ) ≤ 1 / K := by positivity
      linarith
    calc A * Real.exp (-(1 / K)) ≤ A * 1 := mul_le_mul_of_nonneg_left he hApos.le
      _ = A := mul_one A
  have hAU : A ≤ U := by
    rw [hU]
    have he : (1:ℝ) ≤ Real.exp (1 / K) := Real.one_le_exp (by positivity)
    calc A = A * 1 := (mul_one A).symm
      _ ≤ A * Real.exp (1 / K) := mul_le_mul_of_nonneg_left he hApos.le
  have hunion : ∑ p ∈ (Work.BMF.primesIn L A) ∪ (Work.BMF.primesIn A U), (1:ℝ)/(p:ℝ)
      ≤ ∑ p ∈ Work.BMF.primesIn L A, (1:ℝ)/(p:ℝ)
        + ∑ p ∈ Work.BMF.primesIn A U, (1:ℝ)/(p:ℝ) :=
    sum_union_le_of_nonneg _ _ _ (fun p => by positivity)
  have hs := sum_inv_primes_le L A hLpos hLA
  have ht := sum_inv_primes_le A U hApos hAU
  calc
    ∑ p ∈ (Work.BMF.primesIn (A * Real.exp (-(1 / K))) A) ∪
            (Work.BMF.primesIn A (A * Real.exp (1 / K))), (1 : ℝ) / (p : ℝ)
        = ∑ p ∈ (Work.BMF.primesIn L A) ∪ (Work.BMF.primesIn A U), (1:ℝ)/(p:ℝ) := by
          rw [hL, hU]
    _ ≤ (A + 1 - L)/L + (U + 1 - A)/A := le_trans hunion (add_le_add hs ht)
    _ = (A + 1 - A*Real.exp (-(1/K)))/(A*Real.exp (-(1/K)))
          + (A*Real.exp (1/K) + 1 - A)/A := by rw [hL, hU]
    _ ≤ 16*(1/K+1/A) := sum_inv_primes_near_arith A K hApos hK

end Work.BMF.mr_direct
