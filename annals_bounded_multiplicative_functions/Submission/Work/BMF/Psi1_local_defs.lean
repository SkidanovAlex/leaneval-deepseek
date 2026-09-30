import Mathlib
import Submission.Work.BMF.Psi1_L2_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Log-dyadic block bookkeeping for `Work.BMF.Psi1_L2_local_mass`

The target lemma bounds `∑_q (log q)/q^(1+α) * pairK (log p - log q)` (over primes `q`)
by `C * p^(-α)`, uniformly in `α ∈ (0,1]` and the prime `p`.

The proof decomposes the sum according to the **log-dyadic block** of `q`:
`blkIdx q = Nat.clog 2 q`, so that `q ∈ (2^(blkIdx q - 1), 2^(blkIdx q)]`.
Every prime `q ≥ 2` thus sits in exactly one block `(2^(k-1), 2^k]`, `k = blkIdx q ≥ 1`.

* `blkCount k` is the number of primes in the block `k`; Chebyshev's bound gives
  `blkCount k ≤ C * 2^k / k` (`Work.BMF.block_prime_count`).
* `blkBound α j k` bounds the summand `(log q)/q^(1+α) * pairK (log p - log q)` for every
  prime `q` in block `k`, where `j = blkIdx p` is the block of `p`
  (`Work.BMF.prime_weight_block_bound`).  The kernel factor `pairK (log p - log q)` contributes
  `exp (-(log 2)^2 * (max 0 (|j - k| - 1))^2)`, whence the decay in `|j - k|`.
* `serTerm α j k` is the remaining decaying series term.
-/

namespace Work.BMF

open Real

noncomputable section

/-- Log-dyadic block index of `q`: `Nat.clog 2 q`, so that `2^(blkIdx q - 1) < q ≤ 2^(blkIdx q)`
for `q ≥ 2`. -/
noncomputable def blkIdx (q : ℕ) : ℕ := Nat.clog 2 q

/-- Number of primes in the block `(2^(k-1), 2^k]`. -/
noncomputable def blkCount (k : ℕ) : ℝ :=
  ((((Finset.Ioc (2 ^ (k - 1)) (2 ^ k)).filter Nat.Prime).card : ℕ) : ℝ)

/-- Pointwise bound for the summand `(log q)/q^(1+α) * pairK (log p - log q)` on the block of
index `k`, when `p` lies in the block of index `j`. -/
noncomputable def blkBound (α : ℝ) (j k : ℕ) : ℝ :=
  4 * ((k : ℝ) * Real.log 2) * (2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ) * α) *
    Real.exp (-(Real.log 2) ^ 2 * (max 0 (|(j : ℝ) - (k : ℝ)| - 1)) ^ 2)

/-- The decaying series term attached to the block `k`, when `p` lies in the block `j`. -/
noncomputable def serTerm (α : ℝ) (j k : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(k : ℝ) * α) *
    Real.exp (-(Real.log 2) ^ 2 * (max 0 (|(j : ℝ) - (k : ℝ)| - 1)) ^ 2)

lemma blkIdx_eq (q : ℕ) : blkIdx q = Nat.clog 2 q := rfl

/-- Block membership: a number `q ≥ 2` lies in the half-open dyadic interval
`(2^(blkIdx q - 1), 2^(blkIdx q)]`. -/
lemma blkIdx_spec {q : ℕ} (hq : 1 < q) :
    2 ^ (blkIdx q - 1) < q ∧ q ≤ 2 ^ blkIdx q :=
  ⟨Nat.pow_pred_clog_lt_self (by norm_num) hq, Nat.le_pow_clog (by norm_num) q⟩

lemma one_le_blkIdx_of_prime {q : ℕ} (hq : q.Prime) : 1 ≤ blkIdx q :=
  Nat.succ_le_iff.mpr (Nat.clog_pos (by norm_num) hq.one_lt)

/-- Primes of the block `k` are exactly the primes of `(2^(k-1), 2^k]`. -/
lemma mem_block_of_prime_of_blkIdx_eq {q k : ℕ} (hq : q.Prime) (hk : blkIdx q = k) :
    2 ^ (k - 1) < q ∧ q ≤ 2 ^ k := by
  obtain ⟨h1, h2⟩ := blkIdx_spec hq.one_lt
  exact ⟨hk ▸ h1, hk ▸ h2⟩

lemma blkCount_nonneg (k : ℕ) : 0 ≤ blkCount k := by
  rw [blkCount]; positivity

lemma blkCount_zero : blkCount 0 = 0 := by
  rw [blkCount]
  simp

lemma blkBound_nonneg (α : ℝ) (j k : ℕ) : 0 ≤ blkBound α j k := by
  rw [blkBound]
  have h : (0 : ℝ) < 2 := by norm_num
  positivity

lemma serTerm_nonneg (α : ℝ) (j k : ℕ) : 0 ≤ serTerm α j k := by
  rw [serTerm]
  positivity

/-- `log 2 ≥ 1/2`. -/
lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]] at h
  linarith

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

end

end Work.BMF
