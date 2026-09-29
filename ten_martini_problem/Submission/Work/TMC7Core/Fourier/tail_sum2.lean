import Mathlib

namespace Work.TMC7Core.Fourier

open Finset

/-- Elementary tail estimate for the `p`-series with `p = 2`: the sum of `1/n²` over the
integers `n` with `|n| > K` is summable and bounded by `2/K`.

The proof splits the sum over `ℤ` into the two sums over `ℕ` (`n` and `-(n+1)`), evaluates
each of them by the telescoping bound `∑_{K < i < N} 1/i² ≤ 1/K - 1/(N-1) ≤ 1/K`
(`sum_Ioc_inv_sq_le_sub`), and adds the two estimates. -/
theorem tail_sum2 (K : ℕ) (hK : 0 < K) :
    Summable (fun m : ℤ => if (K : ℤ) < |m| then (1 : ℝ) / ((m : ℝ) ^ 2) else 0) ∧
      ∑' m : ℤ, (if (K : ℤ) < |m| then (1 : ℝ) / ((m : ℝ) ^ 2) else 0) ≤ 2 / (K : ℝ) := by
  have key : Summable (fun m : ℤ => if (K : ℤ) < |m| then (1 : ℝ) / ((m : ℝ) ^ 2) else 0) ∧
      ∑' m : ℤ, (if (K : ℤ) < |m| then (1 : ℝ) / ((m : ℝ) ^ 2) else 0) ≤ 2 / (K : ℝ) := by
    set f : ℤ → ℝ := fun m => if (K : ℤ) < |m| then (1 : ℝ) / ((m : ℝ) ^ 2) else 0 with hf
    set Q : ℕ → ℝ := fun n => if K < n then (1 : ℝ) / ((n : ℝ) ^ 2) else 0 with hQ
    -- Bound on the partial sums of `Q`: only the indices `i` with `K < i < N` contribute,
    -- and those contribute at most `∑_{K < i < N} 1/i ^ 2 ≤ 1/K - 1/(N-1) ≤ 1/K`.
    have hrange : ∀ N : ℕ, ∑ i ∈ Finset.range N, Q i ≤ (K : ℝ)⁻¹ := by
      intro N
      have hQ' : ∀ i : ℕ, Q i = (if K < i then ((i : ℝ) ^ 2)⁻¹ else 0) := by
        intro i; rw [hQ]; simp only [one_div]
      simp only [hQ']
      have hfilt : (Finset.range N).filter (fun i => K < i) = Finset.Ioo K N := by
        ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]; omega
      rw [← Finset.sum_filter, hfilt]
      by_cases h : N ≤ K+1
      · have hE : Finset.Ioo K N = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi; simp only [Finset.mem_Ioo] at hi; omega
        rw [hE, Finset.sum_empty]; positivity
      · have hI : Finset.Ioo K N = Finset.Ioc K (N-1) := by
          ext i; simp only [Finset.mem_Ioo, Finset.mem_Ioc]; omega
        rw [hI]
        refine le_trans (sum_Ioc_inv_sq_le_sub (k := K) (n := N-1) (by omega) (by omega)) ?_
        apply sub_le_self; positivity
    have hQnonneg : ∀ n : ℕ, 0 ≤ Q n := by
      intro n
      rw [hQ]
      by_cases h : K < n <;> simp only [h, reduceIte] <;> positivity
    have hQsum : Summable Q := summable_of_sum_range_le hQnonneg hrange
    have hQle : ∑' n : ℕ, Q n ≤ (K : ℝ)⁻¹ := hQsum.tsum_le_of_sum_range_le hrange
    -- The same bound for the shifted series `Q (·+1)`, i.e. for the negative residues.
    have hshift : ∑' n : ℕ, Q (n+1) ≤ (K : ℝ)⁻¹ := by
      have h1 := Summable.sum_add_tsum_nat_add (f := Q) 1 hQsum
      have h0 : Q 0 = 0 := by simp [hQ]
      rw [Finset.sum_range_one, h0, zero_add] at h1
      rw [h1]; exact hQle
    -- Identification of the two `ℕ`-sums drawn from the `ℤ`-indexed series with `Q`.
    have hfn : ∀ n : ℕ, f (n : ℤ) = Q n := by
      intro n
      rw [hf, hQ]; simp only []
      have ha : |((n:ℤ))| = (n:ℤ) := by simp
      rw [ha]
      simp only [Int.ofNat_lt, Int.cast_natCast]
    have hfneg : ∀ n : ℕ, f (-(n+1)) = Q (n+1) := by
      intro n
      rw [hf, hQ]; simp only []
      have ha : |((-(n+1) : ℤ))| = ((n+1 : ℕ) : ℤ) := by
        rw [Int.abs_eq_natAbs]
        have h : ((-(n+1) : ℤ)).natAbs = n+1 := by
          rw [show (-(n+1) : ℤ) = -((n+1 : ℕ) : ℤ) by push_cast; ring,
            Int.natAbs_neg, Int.natAbs_natCast]
        rw [h]
      rw [ha]
      have hc : (((-(n+1) : ℤ)) : ℝ) = -((n+1 : ℕ) : ℝ) := by push_cast; ring
      rw [hc]
      simp only [Int.ofNat_lt, neg_sq]
    have hsum_nat : Summable (fun n : ℕ => f (n : ℤ)) := hQsum.congr (fun n => (hfn n).symm)
    have hQshift_sum : Summable (fun n : ℕ => Q (n+1)) := (summable_nat_add_iff 1).mpr hQsum
    have hsum_neg : Summable (fun n : ℕ => f (-(n+1))) :=
      hQshift_sum.congr (fun n => (hfneg n).symm)
    have htsum : ∑' m : ℤ, f m = ∑' n : ℕ, f n + ∑' n : ℕ, f (-(n+1)) :=
      tsum_of_nat_of_neg_add_one hsum_nat hsum_neg
    have hbound_nat : ∑' n : ℕ, f (n : ℤ) ≤ (K : ℝ)⁻¹ := by
      rw [tsum_congr (fun n => hfn n)]; exact hQle
    have hbound_neg : ∑' n : ℕ, f (-(n+1)) ≤ (K : ℝ)⁻¹ := by
      rw [tsum_congr (fun n => hfneg n)]; exact hshift
    refine ⟨Summable.of_nat_of_neg_add_one hsum_nat hsum_neg, ?_⟩
    calc ∑' m : ℤ, f m = ∑' n : ℕ, f n + ∑' n : ℕ, f (-(n+1)) := htsum
      _ ≤ (K : ℝ)⁻¹ + (K : ℝ)⁻¹ := add_le_add hbound_nat hbound_neg
      _ = 2 / (K : ℝ) := by rw [div_eq_mul_inv]; ring
  exact key

end Work.TMC7Core.Fourier
