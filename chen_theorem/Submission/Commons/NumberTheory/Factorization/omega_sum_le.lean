import Mathlib.NumberTheory.Harmonic.Bounds
import Submission.Commons.NumberTheory.Nat.omega_color_sum_le_harmonic

open scoped BigOperators

namespace Commons.NumberTheory.Factorization

noncomputable section

/-- `1 ≤ 2^n` for all natural `n`. -/
private lemma one_le_two_pow (n : ℕ) : 1 ≤ 2 ^ n := by
  exact one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)

/-- `n ≤ 2^n` for all natural `n`. -/
private lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : (1 : ℕ) ≤ 2 ^ n := one_le_two_pow n
      calc
        n + 1 ≤ 2 ^ n + 1 := by omega
        _ ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by ring

/-- Casting `n ≤ 2^n` to the reals. -/
private lemma nat_le_two_pow_real (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ n := by
  exact_mod_cast (nat_le_two_pow n)

/-- The harmonic partial sum `∑_{k=1}^{Q} 1/k` is at most `1 + log Q` (reals). -/
private lemma harm_Icc_le_one_add_log (Q : ℕ) :
    (∑ k ∈ Finset.Icc 1 Q, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log (Q : ℝ) := by
  have h := (harmonic_le_one_add_log Q : (harmonic Q : ℝ) ≤ 1 + Real.log (Q : ℝ))
  rw [harmonic_eq_sum_Icc] at h
  simpa using h

theorem omega_sum_le :
    ∃ C : ℝ, 0 < C ∧
    ∀ Q : ℕ, 2 ≤ Q →
      (∑ q ∈ Finset.Icc 1 Q, (q.factorization.support.card : ℝ)) ≤
        C * (Q : ℝ) * (Real.log (Q : ℝ) + 1) := by
  refine ⟨1, by norm_num, ?_⟩
  intro Q hQ
  have hQ1 : 1 ≤ Q := by omega
  -- per-term `ω q ≤ 2 ^ ω q` (with `ω q = (q.primeFactors).card`)
  have hterm : ∀ q ∈ Finset.Icc 1 Q,
      (q.primeFactors.card : ℝ) ≤ (2 : ℝ) ^ q.primeFactors.card := by
    intro q hq
    exact nat_le_two_pow_real q.primeFactors.card
  have hstep1 :
      (∑ q ∈ Finset.Icc 1 Q, (q.primeFactors.card : ℝ)) ≤
        ∑ q ∈ Finset.Icc 1 Q, (2 : ℝ) ^ q.primeFactors.card := by
    exact Finset.sum_le_sum hterm
  have hstep2 :
      (∑ q ∈ Finset.Icc 1 Q, (2 : ℝ) ^ q.primeFactors.card) ≤
        (Q : ℝ) * (∑ k ∈ Finset.Icc 1 Q, (1 : ℝ) / (k : ℝ)) := by
    have hh := Commons.NumberTheory.Nat.omega_color_sum_le_harmonic 2 Q
      (by norm_num : (1 : ℕ) ≤ 2) hQ1
    simpa using hh
  have hstep3 :
      (Q : ℝ) * (∑ k ∈ Finset.Icc 1 Q, (1 : ℝ) / (k : ℝ)) ≤
        (Q : ℝ) * (1 + Real.log (Q : ℝ)) := by
    exact mul_le_mul_of_nonneg_left (harm_Icc_le_one_add_log Q) (by positivity)
  calc
    (∑ q ∈ Finset.Icc 1 Q, (q.factorization.support.card : ℝ))
        = ∑ q ∈ Finset.Icc 1 Q, (q.primeFactors.card : ℝ) := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [Nat.support_factorization]
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, (2 : ℝ) ^ q.primeFactors.card := hstep1
    _ ≤ (Q : ℝ) * (∑ k ∈ Finset.Icc 1 Q, (1 : ℝ) / (k : ℝ)) := hstep2
    _ ≤ (Q : ℝ) * (1 + Real.log (Q : ℝ)) := hstep3
    _ = (1 : ℝ) * (Q : ℝ) * (Real.log (Q : ℝ) + 1) := by ring

end

end Commons.NumberTheory.Factorization