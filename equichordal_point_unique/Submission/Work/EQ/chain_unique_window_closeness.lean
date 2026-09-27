import Mathlib
import Submission.Work.EQ.chain_unique_window
import Submission.Work.EQ.chain_step_unique
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.eqLam_ne_zero_of_injOn

namespace Work.EQ

/-- **Uniqueness of chains with equal `ψ₁` and close windows, `ε`-free form.**

This is `Work.EQ.chain_unique_window` (`Submission/Work/EQ/chain_unique_window.lean`) with the
auxiliary chain `p` removed: instead of comparing both chains to a fixed `p` (which forces the
caller to produce a uniform `ε`), the two chains are compared to each other inside the window
(distance `< 1/2`) and each chain is assumed to satisfy the two *ball* hypotheses
`λ^M q.2.2 ∈ ball 0 ρg`, `λ^M q'.2.2 ∈ ball 0 ρg` directly.

Proof: rerun the proof of `Work.EQ.chain_unique_window` with `p := q` and `ε := 1/2`.  The
descending step at index `j` uses `Work.EQ.chain_step_unique` (which needs only `2ε ≤ 1`) with
`‖q.1 j - q.1 j‖ = 0 < 1/2` and `‖q'.1 j - q.1 j‖ < 1/2` (from the window hypothesis, via
`norm_sub_rev`); the index bounds `-M ≤ j ≤ N - 1` give `|j| ≤ K` from `hNK`, `hMK`.  At the end,
`hback M le_rfl : q.1 (-M) = ugermC a h (λ^M q.2.2)` and `-M ≤ K` puts the window equality at
index `-M`; the second coordinates of `ugermC` and `germC` agree, so the injectivity of
`(germC a h ·).2` on `ball 0 ρg`, applied to `λ^M q.2.2` and `λ^M q'.2.2` (in the ball by the two
direct hypotheses), gives `q.2.2 = q'.2.2` after dividing by `λ^M ≠ 0`
(`Work.EQ.eqLam_ne_zero_of_injOn`).  Then the tails plus `q.2.1 = q'.2.1` give the rest. -/
theorem chain_unique_window_closeness {a : ℝ} {h : ℂ → ℂ} {N M K : ℕ} (hNK : N ≤ K)
    (hMK : M ≤ K) {ρg : ℝ} (hρg : 0 < ρg)
    (hinj : Set.InjOn (fun u => (germC a h u).2) (Metric.ball (0 : ℂ) ρg)) :
    ∀ q q' : ChainData, IsChain a h q → IsChain a h q' → q.2.1 = q'.2.1 →
      (∀ k : ℤ, |k| ≤ (K : ℤ) → ‖q.1 k - q'.1 k‖ < 1 / 2) →
      (eqLam a : ℂ) ^ M * q.2.2 ∈ Metric.ball (0 : ℂ) ρg →
      (eqLam a : ℂ) ^ M * q'.2.2 ∈ Metric.ball (0 : ℂ) ρg →
      (∀ n : ℕ, N ≤ n → q.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * q.2.1)) →
      (∀ n : ℕ, N ≤ n → q'.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * q'.2.1)) →
      (∀ n : ℕ, M ≤ n → q.1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * q.2.2)) →
      (∀ n : ℕ, M ≤ n → q'.1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * q'.2.2)) →
      q = q' := by
  -- `eqLam a ≠ 0`, otherwise the second coordinate of `germC a h` is identically zero and the
  -- injectivity hypothesis fails.
  have hlam : eqLam a ≠ 0 := eqLam_ne_zero_of_injOn hρg hinj
  intro q q' hqc hq'c hpsi1 hclose hball hball' htail htail' hback hback'
  -- ### The descent step, with the index bound `|j| ≤ K` discharged from the window.
  -- Compare `q` and `q'` both to the chain `q` itself (distance `0 < 1/2`), so that
  -- `chain_step_unique` applies with `ε = 1/2`.
  have hstep : ∀ j : ℤ, -((M : ℤ)) ≤ j → j ≤ (N : ℤ) - 1 →
      q.1 (j + 1) = q'.1 (j + 1) → q.1 j = q'.1 j := by
    intro j hjM hjNm hnext
    have hMK' : (M : ℤ) ≤ (K : ℤ) := by exact_mod_cast hMK
    have hNK' : (N : ℤ) ≤ (K : ℤ) := by exact_mod_cast hNK
    have hjK : |j| ≤ (K : ℤ) := by
      rw [abs_le]
      omega
    refine chain_step_unique (p := q) hqc hq'c hnext ?_ ?_ (by norm_num : 2 * (1 / 2 : ℝ) ≤ 1)
    · rw [sub_self, norm_zero]; norm_num
    · rw [norm_sub_rev]
      exact hclose j hjK
  -- ### Descending induction from index `N`.
  have key : ∀ k : ℕ, ∀ j : ℤ, j = (N : ℤ) - (k : ℤ) → -((M : ℤ)) ≤ j → q.1 j = q'.1 j := by
    intro k
    induction k with
    | zero =>
      intro j hj hM
      have hjN : j = (N : ℤ) := by omega
      rw [hjN, htail N le_rfl, htail' N le_rfl, hpsi1]
    | succ k ih =>
      intro j hj hM
      have hj' : j + 1 = (N : ℤ) - (k : ℤ) := by omega
      have hM' : -((M : ℤ)) ≤ j + 1 := by omega
      have hnext : q.1 (j + 1) = q'.1 (j + 1) := ih (j + 1) hj' hM'
      have hjNm : j ≤ (N : ℤ) - 1 := by omega
      exact hstep j hM hjNm hnext
  have main : ∀ j : ℤ, -((M : ℤ)) ≤ j → j ≤ (N : ℤ) → q.1 j = q'.1 j := by
    intro j hjM hjN
    obtain ⟨k, hk⟩ : ∃ k : ℕ, j = (N : ℤ) - (k : ℤ) := by
      refine ⟨((N : ℤ) - j).toNat, ?_⟩
      have h0 : (0 : ℤ) ≤ (N : ℤ) - j := by omega
      rw [Int.toNat_of_nonneg h0]
      ring
    exact key k j hk hjM
  -- ### The second linearising parameter at `j = -M`.
  have hpsi2 : q.2.2 = q'.2.2 := by
    have hm : q.1 (-(M : ℤ)) = q'.1 (-(M : ℤ)) := main _ le_rfl (by omega)
    have hsnd : (germC a h ((eqLam a : ℂ) ^ M * q.2.2)).2
        = (germC a h ((eqLam a : ℂ) ^ M * q'.2.2)).2 := by
      have h := congrArg Prod.snd
        ((hback M le_rfl).symm.trans (hm.trans (hback' M le_rfl)))
      simpa [ugermC, eqMirror] using h
    have heq : (eqLam a : ℂ) ^ M * q.2.2 = (eqLam a : ℂ) ^ M * q'.2.2 := hinj hball hball' hsnd
    have hpow : (eqLam a : ℂ) ^ M ≠ 0 := by
      apply pow_ne_zero
      simpa using hlam
    have h0 : (eqLam a : ℂ) ^ M * (q.2.2 - q'.2.2) = 0 := by rw [mul_sub, heq, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hpow
    · exact sub_eq_zero.mp h
  -- ### Everything else is the two tails.
  have hfun : q.1 = q'.1 := by
    funext j
    rcases lt_or_ge j ((N : ℤ)) with hjN | hjN
    · rcases le_or_gt j (-((M : ℤ))) with hjM | hjM
      · -- backward tail
        have hnj : (((-j).toNat : ℕ) : ℤ) = -j := Int.toNat_of_nonneg (by omega)
        have hjn : j = -(((-j).toNat : ℕ) : ℤ) := by omega
        rw [hjn]
        have hMn : M ≤ (-j).toNat := by omega
        rw [hback (-j).toNat hMn, hback' (-j).toNat hMn, hpsi2]
      · -- in the window
        exact main j (by omega) (by omega)
    · -- forward tail
      have hnj : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg (by omega)
      rw [← hnj]
      have hNn : N ≤ j.toNat := by omega
      rw [htail j.toNat hNn, htail' j.toNat hNn, hpsi1]
  exact Prod.ext hfun (Prod.ext hpsi1 hpsi2)


end Work.EQ
