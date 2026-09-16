import Mathlib.NumberTheory.Chebyshev

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Chebyshev

private lemma theta_nat_eq_sum_Ioc (n : ℕ) :
    Chebyshev.theta (n : ℝ)
      = ∑ m ∈ Finset.Ioc 0 n, (if m.Prime then Real.log (m : ℝ) else 0) := by
  unfold Chebyshev.theta
  rw [Nat.floor_natCast, ← Finset.sum_filter]

theorem sum_Icc_prime_log_eq_theta_sub (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0))
      = Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ)
        + (if a.Prime then Real.log (a : ℝ) else 0) := by
  rw [theta_nat_eq_sum_Ioc b, theta_nat_eq_sum_Ioc a]
  have hsub : Finset.Ioc 0 a ⊆ Finset.Ioc 0 b := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, le_trans hn.2 hab⟩
  have hsdiff : Finset.Ioc 0 b \ Finset.Ioc 0 a = Finset.Ioc a b := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Ioc]
    omega
  have hIcc : (∑ m ∈ Finset.Icc a b, (if m.Prime then Real.log (m : ℝ) else 0))
      = (if a.Prime then Real.log (a : ℝ) else 0)
        + ∑ m ∈ Finset.Ioc a b, (if m.Prime then Real.log (m : ℝ) else 0) := by
    rw [Finset.Icc_eq_cons_Ioc hab, Finset.sum_cons]
  have hsum : (∑ m ∈ Finset.Ioc 0 b, (if m.Prime then Real.log (m : ℝ) else 0))
      - (∑ m ∈ Finset.Ioc 0 a, (if m.Prime then Real.log (m : ℝ) else 0))
      = ∑ m ∈ Finset.Ioc a b, (if m.Prime then Real.log (m : ℝ) else 0) := by
    rw [← hsdiff, ← Finset.sum_sdiff hsub]
    ring
  rw [hIcc, hsum]
  ring

end Commons.NumberTheory.Chebyshev
