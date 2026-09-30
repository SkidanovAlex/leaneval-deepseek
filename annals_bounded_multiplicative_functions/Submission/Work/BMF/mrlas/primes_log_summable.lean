import Mathlib
import Submission.Work.BMF.mrlas.Psi2_defs
import Submission.Work.BMF.mrlas.log_mul_rpow_neg_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Convergence of `∑_p log p · p^{-2σ}` over the primes, uniformly in `σ ≥ 1`

For every prime `p` and every `σ ≥ 1` the general term `log p · p^{-2σ}` is bounded by
`p^{-3/2}` (because `log p ≤ p^{1/2}` and `p^{-2σ} ≤ p^{-2}`).  Since `∑_n n^{-3/2}`
converges, comparison gives both summability of the prime series and a bound on its sum
that is uniform in `σ ≥ 1`.
-/

namespace Work.BMF.mrlas

open scoped BigOperators

/-- The sum over the primes is dominated by the same sum over all natural numbers. -/
theorem summ_primes_le_summ_nat (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (h : Summable f) :
    (∑' p : Nat.Primes, f p) ≤ ∑' n : ℕ, f n := by
  exact Summable.tsum_subtype_le f {n : ℕ | n.Prime} hf h

theorem primes_log_summable : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℝ, 1 ≤ σ →
    Summable (fun p : Nat.Primes => Real.log p * (p : ℝ) ^ (-2 * σ)) ∧
    (∑' p : Nat.Primes, Real.log p * (p : ℝ) ^ (-2 * σ)) ≤ K := by
  refine ⟨∑' n : ℕ, (n : ℝ) ^ (-(3 : ℝ) / 2), ?_, ?_⟩
  · exact tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · intro σ hσ
    have hFsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ) / 2)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    have hFsub : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(3 : ℝ) / 2)) :=
      hFsum.subtype (fun n => n.Prime)
    have hf : Summable (fun p : Nat.Primes => Real.log p * (p : ℝ) ^ (-2 * σ)) :=
      Summable.of_nonneg_of_le
        (fun p => mul_nonneg (Real.log_nonneg (by exact_mod_cast p.2.one_lt.le))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (fun p => log_mul_rpow_neg_le p.2.one_lt.le hσ) hFsub
    have hb1 : (∑' p : Nat.Primes, Real.log p * (p : ℝ) ^ (-2 * σ)) ≤
        ∑' p : Nat.Primes, (p : ℝ) ^ (-(3 : ℝ) / 2) :=
      hf.tsum_le_tsum (fun p => log_mul_rpow_neg_le p.2.one_lt.le hσ) hFsub
    have hb2 : (∑' p : Nat.Primes, (p : ℝ) ^ (-(3 : ℝ) / 2)) ≤
        ∑' n : ℕ, (n : ℝ) ^ (-(3 : ℝ) / 2) :=
      summ_primes_le_summ_nat _ (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) hFsum
    exact ⟨hf, le_trans hb1 hb2⟩

end Work.BMF.mrlas
