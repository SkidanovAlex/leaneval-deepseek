/-
# `Submission.Work.FIArea1.Helpers` — elementary estimates for area 1 (*FI* §5)

Small, reusable bounds used by the assembly of `Work.FITop3.Area1` (see `NOTES.md`):

* `ω(n) ≤ log₂ n` (the number of distinct prime factors of `n` is at most `log₂ n`), used to
  replace the paper's `Σ τ(n)ω(n)` by `log₂(2N) · Σ τ(n)` in the trivial bound for (5.10);
* `Σ_{p ∈ s}(1 + B/(pA)) ≤ #s (1 + B/(PA))` for `P ≤ p`, used to replace `1/p` by `1/Pz`
  (`Pz` = the sieve level `P` of (4.4), and `NoSmallPrimes` says every prime divisor of `|z|²`
  exceeds `Pz`).
-/
import Mathlib
import Submission.Work.FIArea1.Basic

set_option autoImplicit false

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `2 ^ #{p : p prime, p ∣ n} ≤ n` for `n ≥ 1`: each prime factor is `≥ 2`. -/
lemma two_pow_card_primeFactors_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ n.primeFactors.card ≤ n := by
  have h1 : 2 ^ n.primeFactors.card = ∏ p ∈ n.primeFactors, (2 : ℕ) := by rw [Finset.prod_const]
  rw [h1]
  calc ∏ p ∈ n.primeFactors, (2 : ℕ) ≤ ∏ p ∈ n.primeFactors, p := by
        refine Finset.prod_le_prod₀ (fun i _ => by norm_num) (fun i hi => ?_)
        exact (Nat.mem_primeFactors.mp hi).1.two_le
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- `ω(n) = #{p : p prime, p ∣ n} ≤ log₂ n`. -/
lemma card_primeFactors_le_log (n : ℕ) (hn : 1 ≤ n) : n.primeFactors.card ≤ Nat.log 2 n := by
  rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
  exact two_pow_card_primeFactors_le n hn

/-- Monotonicity in the argument: `ω(n) ≤ log₂ m` for `n ≤ m`, `1 ≤ n`. -/
lemma card_primeFactors_le_log_of_le {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    n.primeFactors.card ≤ Nat.log 2 m :=
  (card_primeFactors_le_log n hn).trans (Nat.log_mono_right hnm)

/-- `(log₂ m : ℝ) ≤ log m / log 2`: the real form of `ω ≤ log₂` used in the assembly. -/
lemma cast_log_le_log_div (m : ℕ) (hm : 1 ≤ m) :
    (Nat.log 2 m : ℝ) ≤ Real.log m / Real.log 2 := by
  have h2 : (1 : ℝ) < 2 := by norm_num
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hpow : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hpow' : ((2 : ℝ)) ^ Nat.log 2 m ≤ (m : ℝ) := by exact_mod_cast hpow
  have hlog : ((Nat.log 2 m : ℝ)) * Real.log 2 ≤ Real.log m := by
    have := Real.log_le_log (by positivity) hpow'
    rwa [Real.log_pow] at this
  rw [le_div_iff₀ (Real.log_pos h2)]
  linarith

/-- For primes `p ≥ P ≥ 1` and `A > 0`, `B ≥ 0`: the sum of `1 + B/(pA)` over any set of such
primes is at most `#s · (1 + B/(PA))`. -/
lemma sum_p_bound {s : Finset ℕ} {P : ℕ} {A B : ℝ} (hP : 1 ≤ P) (hA : 0 < A) (hB : 0 ≤ B)
    (h : ∀ p ∈ s, P ≤ p) :
    ∑ p ∈ s, (1 + B / ((p : ℝ) * A)) ≤ s.card * (1 + B / ((P : ℝ) * A)) := by
  calc ∑ p ∈ s, (1 + B / ((p : ℝ) * A))
      ≤ ∑ _p ∈ s, (1 + B / ((P : ℝ) * A)) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        have hpP : P ≤ p := h p hp
        have hp1 : 1 ≤ p := le_trans hP hpP
        have hle : (P : ℝ) * A ≤ (p : ℝ) * A := by
          have h' : (P : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpP
          exact mul_le_mul_of_nonneg_right h' hA.le
        have hpos : 0 < (P : ℝ) * A := by positivity
        have : B / ((p : ℝ) * A) ≤ B / ((P : ℝ) * A) := by gcongr
        linarith
    _ = s.card * (1 + B / ((P : ℝ) * A)) := by rw [Finset.sum_const, nsmul_eq_mul]

end

end Work.FIArea1
