import Mathlib
import Submission.Work.BMF.Psi1_L2_defs
import Submission.Work.BMF.Psi1_local_defs
import Submission.Work.BMF.block_prime_count
import Submission.Work.BMF.prime_weight_block_bound
import Submission.Work.BMF.log_dyadic_series_bound
import Submission.Work.BMF.blkCount_mul_blkBound_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local `L²` mass of the log-dyadic prime sum

Target (`Work.BMF.Psi1_L2_local_mass`): there is `C > 0` with, for every `α ∈ (0,1]` and every
prime `p`,

`∑_q (if q prime then (log q)/q^(1+α) * pairK (log p - log q) else 0) ≤ C * p^(-α)`.

Proof.  Decompose the sum over the log-dyadic blocks `(2^(k-1), 2^k]`, indexed by
`k = blkIdx q = Nat.clog 2 q`.  Each prime `q` lies in exactly one block `k ≥ 1`, and

* the number of primes in block `k` is `≤ C * 2^k / k` (`Work.BMF.block_prime_count`,
  from Chebyshev's estimate),
* each summand on block `k` is at most `blkBound α (blkIdx p) k`
  (`Work.BMF.prime_weight_block_bound`), whose kernel factor decays like
  `exp (-(log 2)^2 * max 0 (|blkIdx p - k| - 1)^2)`.

Multiplying the two gives the decaying series term `4·C·log 2·serTerm α (blkIdx p) k`
(`Work.BMF.blkCount_mul_blkBound_le`), which summed over the blocks is `O(2^(-j α))` with
`j = blkIdx p` (`Work.BMF.log_dyadic_series_bound`); since `p ≤ 2^j`, this is `O(p^(-α))`.

The finite-sum form of the conclusion is combined with `Real.tsum_le_of_sum_le`.
-/

namespace Work.BMF

open Real

noncomputable section

theorem Psi1_L2_local_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ p : ℕ, p.Prime →
      (∑' q : ℕ, (if q.Prime then
        Real.log q / (q : ℝ) ^ (1 + α) * pairK (Real.log p - Real.log q) else 0))
        ≤ C * (p : ℝ) ^ (-α) := by
  obtain ⟨Cb, hCbpos, hcount⟩ := block_prime_count
  obtain ⟨Cs, hCspos, hseries⟩ := log_dyadic_series_bound
  refine ⟨4 * max Cb 1 * Real.log 2 * Cs, ?_, ?_⟩
  · have h1 : (0:ℝ) < max Cb 1 := lt_of_lt_of_le one_pos (le_max_right Cb 1)
    have h2 : (0:ℝ) < Real.log 2 := log_two_pos
    positivity
  · intro α hα0 hα1 p hp
    set Cb' : ℝ := max Cb 1 with hCb'def
    have hCb'pos : 0 < Cb' := by rw [hCb'def]; exact lt_of_lt_of_le one_pos (le_max_right Cb 1)
    have hCb'ge : Cb ≤ Cb' := by rw [hCb'def]; exact le_max_left Cb 1
    have hcount' : ∀ k : ℕ, 1 ≤ k → blkCount k ≤ Cb' * (2 : ℝ) ^ k / (k : ℝ) := by
      intro k hk
      refine le_trans (hcount k hk) ?_
      have h2k : (0:ℝ) ≤ (2:ℝ)^k := by positivity
      have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCb'ge h2k) hkR.le
    refine Real.tsum_le_of_sum_le (f := fun q : ℕ => (if q.Prime then
        Real.log q / (q : ℝ) ^ (1 + α) * pairK (Real.log p - Real.log q) else 0)) ?_ ?_
    · intro q
      by_cases hq : q.Prime
      · simp only [hq, if_true]
        refine mul_nonneg (div_nonneg ?_ ?_) (pairK_nonneg _)
        · exact Real.log_nonneg (by exact_mod_cast hq.one_lt.le)
        · exact Real.rpow_nonneg (by positivity) _
      · simp only [hq, if_false]
        exact le_refl 0
    intro F
    set j : ℕ := blkIdx p with hjdef
    set A : ℕ → ℝ := fun q => Real.log q / (q : ℝ) ^ (1 + α) * pairK (Real.log p - Real.log q) with hAdef
    set FP : Finset ℕ := F.filter Nat.Prime with hFPdef
    have step1 : ∑ q ∈ F, (if q.Prime then
        Real.log q / (q : ℝ) ^ (1 + α) * pairK (Real.log p - Real.log q) else 0)
        = ∑ q ∈ FP, A q := by
      rw [hFPdef]
      exact (Finset.sum_filter (fun q => Nat.Prime q)
        (fun q => Real.log q / (q : ℝ) ^ (1 + α) * pairK (Real.log p - Real.log q))).symm
    have step2 : ∑ q ∈ FP, A q
        = ∑ k ∈ FP.image blkIdx, ∑ q ∈ FP.filter (fun q => blkIdx q = k), A q :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) A).symm
    have step3 : ∀ k ∈ FP.image blkIdx,
        ∑ q ∈ FP.filter (fun q => blkIdx q = k), A q ≤ 4 * Cb' * Real.log 2 * serTerm α j k := by
      intro k hk
      have hk1 : 1 ≤ k := by
        rw [Finset.mem_image] at hk
        obtain ⟨q, hq, rfl⟩ := hk
        rw [Finset.mem_filter] at hq
        exact one_le_blkIdx_of_prime hq.2
      have hfib : ∑ q ∈ FP.filter (fun q => blkIdx q = k), A q ≤ blkCount k * blkBound α j k := by
        have hsub : FP.filter (fun q => blkIdx q = k) ⊆
            (Finset.Ioc (2 ^ (k - 1)) (2 ^ k)).filter Nat.Prime := by
          intro q hq
          rw [Finset.mem_filter] at hq
          obtain ⟨hqFP, hqk⟩ := hq
          rw [hFPdef, Finset.mem_filter] at hqFP
          obtain ⟨_, hqp⟩ := hqFP
          rw [Finset.mem_filter]
          obtain ⟨h1, h2⟩ := mem_block_of_prime_of_blkIdx_eq hqp hqk
          exact ⟨Finset.mem_Ioc.mpr ⟨h1, h2⟩, hqp⟩
        have hcard : (FP.filter (fun q => blkIdx q = k)).card ≤
            ((Finset.Ioc (2 ^ (k - 1)) (2 ^ k)).filter Nat.Prime).card :=
          Finset.card_le_card hsub
        have hpt : ∀ q ∈ FP.filter (fun q => blkIdx q = k), A q ≤ blkBound α j k := by
          intro q hq
          rw [Finset.mem_filter] at hq
          obtain ⟨hqFP, hqk⟩ := hq
          rw [hFPdef, Finset.mem_filter] at hqFP
          obtain ⟨_, hqp⟩ := hqFP
          have hw := prime_weight_block_bound α hα0 hα1 p q hp hqp
          simpa [hAdef, hjdef, hqk] using hw
        calc ∑ q ∈ FP.filter (fun q => blkIdx q = k), A q
            ≤ (FP.filter (fun q => blkIdx q = k)).card • (blkBound α j k) :=
              Finset.sum_le_card_nsmul _ _ _ hpt
          _ ≤ (((Finset.Ioc (2 ^ (k - 1)) (2 ^ k)).filter Nat.Prime).card) • (blkBound α j k) := by
              rw [nsmul_eq_mul, nsmul_eq_mul]
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (blkBound_nonneg α j k)
          _ = blkCount k * blkBound α j k := by
              rw [blkCount, nsmul_eq_mul]
      refine le_trans hfib ?_
      have hc := blkCount_mul_blkBound_le Cb' α hCb'pos hα0 hcount' j k hk1
      rw [hjdef] at hc
      exact hc
    have step4 : ∑ k ∈ FP.image blkIdx, (4 * Cb' * Real.log 2 * serTerm α j k)
        = 4 * Cb' * Real.log 2 * ∑ k ∈ FP.image blkIdx, serTerm α j k := by
      rw [Finset.mul_sum]
    have hconst : 0 ≤ 4 * Cb' * Real.log 2 := by positivity
    have hjle : (p : ℝ) ≤ (2 : ℝ) ^ j := by
      rw [hjdef]
      exact_mod_cast Nat.le_pow_clog (by norm_num) p
    have hple : (2 : ℝ) ^ (-(j : ℝ) * α) ≤ (p : ℝ) ^ (-α) := by
      have heq : (2 : ℝ) ^ (-(j : ℝ) * α) = ((2 : ℝ) ^ j) ^ (-α) := by
        conv_rhs => rw [← Real.rpow_natCast (2:ℝ) j,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ (2:ℝ))]
        rw [show (j : ℝ) * (-α) = -(j : ℝ) * α by ring]
      rw [heq]
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hp.pos) hjle (by linarith)
    calc ∑ q ∈ F, (if q.Prime then
          Real.log q / (q : ℝ) ^ (1 + α) * pairK (Real.log p - Real.log q) else 0)
        = ∑ k ∈ FP.image blkIdx, ∑ q ∈ FP.filter (fun q => blkIdx q = k), A q := by
          rw [step1, step2]
      _ ≤ ∑ k ∈ FP.image blkIdx, (4 * Cb' * Real.log 2 * serTerm α j k) :=
          Finset.sum_le_sum step3
      _ = 4 * Cb' * Real.log 2 * ∑ k ∈ FP.image blkIdx, serTerm α j k := step4
      _ ≤ 4 * Cb' * Real.log 2 * (Cs * (2 : ℝ) ^ (-(j : ℝ) * α)) :=
          mul_le_mul_of_nonneg_left (hseries α hα0 hα1 j _) hconst
      _ = (4 * Cb' * Real.log 2 * Cs) * (2 : ℝ) ^ (-(j : ℝ) * α) := by ring
      _ ≤ (4 * Cb' * Real.log 2 * Cs) * (p : ℝ) ^ (-α) :=
          mul_le_mul_of_nonneg_left hple
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCb'pos.le) log_two_pos.le) hCspos.le)
      _ = (4 * max Cb 1 * Real.log 2 * Cs) * (p : ℝ) ^ (-α) := by rw [hCb'def]


end

end Work.BMF
