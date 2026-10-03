import Mathlib
import Submission.Work.FIChain.TailDefs
import Submission.Work.FIChain.sqfree_divisor_cube_bound

namespace Work.FIChain

/-- **`τ³`-swelling.**  For every `K` with `d ∣ K` the term `a_K · τ(K/d)³` is absorbed by the
`e = 1`-shifted sums: the `3`-power of the divisor function is "swollen" into a sum over small
`e` (`e³ d ≤ x`, the Rankin range), each `e` carrying the weight `(2 τ(e))⁹` and re-collecting all
multiples `de ∣ K` of the original weight.

The pointwise input is `Work.FIChain.sqfree_divisor_cube_bound`: for squarefree `n = K/d` there is a
divisor `e ∣ n` with `e³ ≤ n` and `τ(n)³ ≤ (2 τ(e))⁹` (take `e` the product of the `⌊ω(n)/3⌋`
smallest prime factors).  Since `atilc` vanishes off the squarefree integers and is nonnegative,
that single `e` dominates the corresponding `K`-term; swapping the two sums finishes the job. -/
theorem tau_cube_swell (x d : ℕ) :
    (∑ K ∈ (Finset.Icc 1 x).filter (fun K => d ∣ K),
        Work.FIChain.atilc K * ((K / d).divisors.card : ℝ) ^ 3)
      ≤ ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
          (2 * ((e.divisors.card : ℝ))) ^ 9 *
            ∑ K ∈ (Finset.Icc 1 x).filter (fun K => d * e ∣ K), Work.FIChain.atilc K := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · -- `d = 0`: the left index set is empty (`0 ∣ K` forces `K = 0 ∉ [1,x]`).
    subst hd0
    have h0 : (Finset.Icc 1 x).filter (fun K => 0 ∣ K) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro K hK hdvd
      rw [Finset.mem_Icc] at hK
      rw [zero_dvd_iff] at hdvd
      omega
    rw [h0, Finset.sum_empty]
    apply Finset.sum_nonneg
    intro e he
    apply mul_nonneg (pow_nonneg (by positivity) 9)
    exact Finset.sum_nonneg (fun K _ => Work.FITop.atilFIa_nonneg K)
  · -- `d ≥ 1`.  Pointwise absorption for `K ∈ [1,x]`, `d ∣ K`.
    have hperK : ∀ K ∈ (Finset.Icc 1 x).filter (fun K => d ∣ K),
        Work.FIChain.atilc K * ((K / d).divisors.card : ℝ) ^ 3
        ≤ Work.FIChain.atilc K * (∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
            (if d * e ∣ K then (2 * ((e.divisors.card : ℝ))) ^ 9 else 0)) := by
      intro K hK
      by_cases hK0 : Work.FIChain.atilc K = 0
      · simp [hK0]
      · -- `atilc K ≠ 0` forces `K` squarefree.
        have hsqK : Squarefree K := by
          by_contra hns
          exact hK0 (by simp [Work.FITop.atilFIa_eq_indicator, hns])
        have hdvd : d ∣ K := (Finset.mem_filter.mp hK).2
        obtain ⟨hK1, hKx⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hK).1
        have hKpos : 0 < K := hK1
        have hnpos : 0 < K / d := Nat.div_pos (Nat.le_of_dvd hKpos hdvd) hd
        have hsqn : Squarefree (K / d) :=
          Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hdvd) hsqK
        obtain ⟨e0, he0dvd, he0cube, he0bound⟩ := sqfree_divisor_cube_bound (K / d) hsqn hnpos.ne'
        -- the witness `e0` lies in the Rankin range `e³ d ≤ x`
        have he0mem : e0 ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x) := by
          rw [Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · exact Nat.pos_of_dvd_of_pos he0dvd hnpos
          · exact le_trans (Nat.le_of_dvd hnpos he0dvd) (le_trans (Nat.div_le_self K d) hKx)
          · have h2 : e0 ^ 3 * d ≤ (K / d) * d := Nat.mul_le_mul_right d he0cube
            rw [Nat.div_mul_cancel hdvd] at h2
            exact le_trans h2 hKx
        have he0dvdK : d * e0 ∣ K := by
          rw [← Nat.mul_div_cancel' hdvd]
          exact Nat.mul_dvd_mul_left d he0dvd
        have hboundR : ((K / d).divisors.card : ℝ) ^ 3 ≤ (2 * ((e0.divisors.card : ℝ))) ^ 9 := by
          exact_mod_cast he0bound
        have hsumge : ((K / d).divisors.card : ℝ) ^ 3
            ≤ ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
                (if d * e ∣ K then (2 * ((e.divisors.card : ℝ))) ^ 9 else 0) := by
          calc ((K / d).divisors.card : ℝ) ^ 3
              ≤ (2 * ((e0.divisors.card : ℝ))) ^ 9 := hboundR
            _ = (if d * e0 ∣ K then (2 * ((e0.divisors.card : ℝ))) ^ 9 else 0) :=
                  (if_pos he0dvdK).symm
            _ ≤ ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
                  (if d * e ∣ K then (2 * ((e.divisors.card : ℝ))) ^ 9 else 0) := by
                apply Finset.single_le_sum
                  (f := fun e => (if d * e ∣ K then (2 * ((e.divisors.card : ℝ))) ^ 9 else 0))
                · intro e he
                  by_cases hc : d * e ∣ K
                  · simp only [hc, if_true]; positivity
                  · simp [hc]
                · exact he0mem
        exact mul_le_mul_of_nonneg_left hsumge (Work.FITop.atilFIa_nonneg K)
    -- Sum the pointwise bound and swap the two sums.
    calc (∑ K ∈ (Finset.Icc 1 x).filter (fun K => d ∣ K),
            Work.FIChain.atilc K * ((K / d).divisors.card : ℝ) ^ 3)
        ≤ ∑ K ∈ (Finset.Icc 1 x).filter (fun K => d ∣ K),
            Work.FIChain.atilc K * (∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
              (if d * e ∣ K then (2 * ((e.divisors.card : ℝ))) ^ 9 else 0)) :=
              Finset.sum_le_sum hperK
      _ = ∑ K ∈ (Finset.Icc 1 x).filter (fun K => d ∣ K),
            ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
              Work.FIChain.atilc K * (if d * e ∣ K then (2 * ((e.divisors.card : ℝ))) ^ 9 else 0) := by
            simp_rw [Finset.mul_sum]
      _ = ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
            ∑ K ∈ (Finset.Icc 1 x).filter (fun K => d ∣ K),
              Work.FIChain.atilc K * (if d * e ∣ K then (2 * ((e.divisors.card : ℝ))) ^ 9 else 0) :=
              Finset.sum_comm
      _ = ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
            (2 * ((e.divisors.card : ℝ))) ^ 9 *
              (∑ K ∈ (Finset.Icc 1 x).filter (fun K => d ∣ K),
                (if d * e ∣ K then Work.FIChain.atilc K else 0)) := by
            apply Finset.sum_congr rfl
            intro e he
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro K hK
            by_cases hc : d * e ∣ K
            · simp only [hc, if_true]; ring
            · simp only [hc, if_false]; ring
      _ = ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
            (2 * ((e.divisors.card : ℝ))) ^ 9 *
              (∑ K ∈ ((Finset.Icc 1 x).filter (fun K => d ∣ K)).filter (fun K => d * e ∣ K),
                Work.FIChain.atilc K) := by
            apply Finset.sum_congr rfl
            intro e he
            congr 1
            exact (Finset.sum_filter (s := (Finset.Icc 1 x).filter (fun K => d ∣ K))
              (fun K => d * e ∣ K) (fun K => Work.FIChain.atilc K)).symm
      _ = ∑ e ∈ (Finset.Icc 1 x).filter (fun e => e ^ 3 * d ≤ x),
            (2 * ((e.divisors.card : ℝ))) ^ 9 *
              (∑ K ∈ (Finset.Icc 1 x).filter (fun K => d * e ∣ K),
                Work.FIChain.atilc K) := by
            apply Finset.sum_congr rfl
            intro e he
            have hfilt : ((Finset.Icc 1 x).filter (fun K => d ∣ K)).filter (fun K => d * e ∣ K)
                = (Finset.Icc 1 x).filter (fun K => d * e ∣ K) := by
              rw [Finset.filter_filter]
              apply Finset.filter_congr
              intro K hK
              exact ⟨fun h => h.2, fun h => ⟨dvd_trans (Nat.dvd_mul_right d e) h, h⟩⟩
            rw [hfilt]

end Work.FIChain
