import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.identity_defs

open Classical

namespace Work.ChenPlan.LinearSieve.RI

open Work.ChenPlan.LinearSieve

/-- **Nonvanishing of `T_n` forces `D ≥ 2^{n-2}`.**  If the `n`-th Rosser–Iwaniec layer sum
`T_n(D,z)` does not vanish, then the recursion must have peeled `n` primes `p_1 > ⋯ > p_n ≥ 2`,
each dividing `D` in succession: `D ≥ p_1 p_2 ⋯ p_n ≥ 2^n ≥ 2^{n-2}`.  (For `n = 3` the extra
support condition `Tcond 3 D p` already yields `D ≥ p³ ≥ 2³`.) -/
theorem T_ne_zero_le {A : BoundingSieve} {D z : ℝ} {n : ℕ} (hn : 3 ≤ n)
    (h : T A n D z ≠ 0) : (2 : ℝ) ^ (n - 2) ≤ D := by
  have main : ∀ n : ℕ, 3 ≤ n → ∀ D z : ℝ, T A n D z ≠ 0 → (2:ℝ)^(n-2) ≤ D := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn D z hT
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [T.eq_2 A D z m] at hT
      obtain ⟨p, hp, hpne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
      rw [Finset.mem_filter] at hp
      obtain ⟨hpmem, hpz, hTcond⟩ := hp
      have hpprime : p.Prime := (Nat.mem_primeFactors.mp hpmem).1
      have hppos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpprime.pos
      have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpprime.two_le
      have hTne : T A m (D / (p:ℝ)) (p:ℝ) ≠ 0 := by
        intro hh; rw [hh, mul_zero] at hpne; exact hpne rfl
      by_cases hm2 : m = 2
      · -- base case `n = 3`: the support condition `Tcond 3 D p` gives `p³ ≤ D`
        subst hm2
        have hp3leD : (p:ℝ)^3 ≤ D := hTcond.2 (by norm_num) ⟨1, by norm_num⟩
        have h8 : (8:ℝ) ≤ (p:ℝ)^3 := by
          have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hp2 3
          norm_num at h ⊢; linarith
        have : (2:ℝ) ≤ D := by linarith
        simpa using this
      · -- step: `T A m (D/p) p ≠ 0` with `m ≥ 3`, and `D = (D/p)·p` with `p ≥ 2`
        have hm3 : 3 ≤ m := by omega
        have hih := ih m (by omega) hm3 (D / (p:ℝ)) (p:ℝ) hTne
        have hmul : (2:ℝ)^(m-2) * (p:ℝ) ≤ D := (le_div_iff₀ hppos).mp hih
        have hpow : (2:ℝ)^(m-1) = (2:ℝ)^(m-2) * 2 := by
          rw [show m - 1 = (m - 2) + 1 by omega, pow_succ]
        have hfin : (2:ℝ)^(m-1) ≤ D := by
          calc (2:ℝ)^(m-1) = (2:ℝ)^(m-2) * 2 := hpow
            _ ≤ (2:ℝ)^(m-2) * (p:ℝ) := by
                apply mul_le_mul_of_nonneg_left hp2; positivity
            _ ≤ D := hmul
        simpa [show (m+1)-2 = m-1 by omega] using hfin
  exact main n hn D z h

end Work.ChenPlan.LinearSieve.RI
