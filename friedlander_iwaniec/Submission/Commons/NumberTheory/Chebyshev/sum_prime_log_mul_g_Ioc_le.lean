import Mathlib
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_div_prime_le_log
import Submission.Commons.NumberTheory.Mertens.log_prime_div_prime_ge_log_sub_two

open Finset

namespace Commons.NumberTheory.Chebyshev

/-- Summing over the primes in a half-open band `(y, z]` equals the difference of the
prime sums up to `z` and up to `y`. -/
lemma sum_Ioc_filter_prime_eq_sub (f : ℕ → ℝ) {y z : ℕ} (hyz : y ≤ z) :
    (∑ p ∈ (Finset.Ioc y z).filter Nat.Prime, f p)
      = (∑ p ∈ z.primesLE, f p) - (∑ p ∈ y.primesLE, f p) := by
  have hsub : y.primesLE ⊆ z.primesLE := Nat.primesLE_mono hyz
  have heq : (Finset.Ioc y z).filter Nat.Prime = z.primesLE \ y.primesLE := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Ioc, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hyn, hnz⟩, hp⟩
      exact ⟨⟨hnz, hp⟩, fun h => absurd h.1 (not_le.mpr hyn)⟩
    · rintro ⟨⟨hnz, hp⟩, hny⟩
      exact ⟨⟨lt_of_not_ge (fun h => hny ⟨h, hp⟩), hnz⟩, hp⟩
  have hs := Finset.sum_sdiff (f := f) hsub
  rw [heq]
  linarith

/-- First Mertens inequality in a uniform form valid for every `n ≥ 1`:
`∑_{p ≤ n} (log p)/p ≤ log n`. -/
private lemma primesLE_log_div_le_log (n : ℕ) (hn : 1 ≤ n) :
    (∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ)) ≤ Real.log (n : ℝ) := by
  rcases eq_or_lt_of_le hn with h | h
  · rw [← h, Nat.primesLE_one, Finset.sum_empty]
    simp
  · have h2 : 2 ≤ n := by omega
    have hb := Commons.NumberTheory.Mertens.sum_log_prime_div_prime_le_log (n : ℝ)
      (by exact_mod_cast h2)
    simpa [Nat.floor_natCast] using hb

/-- Companion lower bound, uniform for `n ≥ 1`: `log n - 2 ≤ ∑_{p ≤ n} (log p)/p`. -/
private lemma log_sub_two_le_primesLE_log_div (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n : ℝ) - 2 ≤ ∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ) := by
  rcases eq_or_lt_of_le hn with h | h
  · rw [← h, Nat.primesLE_one, Finset.sum_empty]
    simp
  · have h2 : 2 ≤ n := by omega
    have hb := Commons.NumberTheory.Mertens.log_prime_div_prime_ge_log_sub_two (n : ℝ)
      (by exact_mod_cast h2)
    simpa [Nat.floor_natCast] using hb

/-- Main lemma: if `g` is nonnegative on primes and `g p ≤ C / p`, then the weighted
prime log-sum over a band `(y, z]` is `≪ 1 + log (z / y)`. -/
theorem sum_prime_log_mul_g_Ioc_le {g : ℕ → ℝ}
    (hg0 : ∀ p : ℕ, p.Prime → 0 ≤ g p)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, p.Prime → g p ≤ C / (p : ℝ)) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ y z : ℕ, 1 ≤ y → y ≤ z →
      (∑ p ∈ (Finset.Ioc y z).filter Nat.Prime, Real.log (p : ℝ) * g p)
        ≤ C₀ * (1 + Real.log ((z : ℝ) / (y : ℝ))) := by
  obtain ⟨C, hCpos, hC⟩ := hbound
  refine ⟨2 * C, by positivity, ?_⟩
  intro y z hy hyz
  have hCnn : 0 ≤ C := le_of_lt hCpos
  -- termwise comparison with `C * (log p / p)`
  have hterm : ∀ p ∈ (Finset.Ioc y z).filter Nat.Prime,
      Real.log (p : ℝ) * g p ≤ C * (Real.log (p : ℝ) / (p : ℝ)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hpprime⟩ := hp
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
    calc Real.log (p : ℝ) * g p ≤ Real.log (p : ℝ) * (C / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left (hC p hpprime) hlog
      _ = C * (Real.log (p : ℝ) / (p : ℝ)) := by ring
  have hsum : (∑ p ∈ (Finset.Ioc y z).filter Nat.Prime, Real.log (p : ℝ) * g p)
      ≤ C * (∑ p ∈ (Finset.Ioc y z).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  rw [sum_Ioc_filter_prime_eq_sub (fun p => Real.log (p : ℝ) / (p : ℝ)) hyz] at hsum
  refine le_trans hsum ?_
  have hz1 : 1 ≤ z := le_trans hy hyz
  have hAz : (∑ p ∈ z.primesLE, Real.log (p : ℝ) / (p : ℝ)) ≤ Real.log (z : ℝ) :=
    primesLE_log_div_le_log z hz1
  have hAy : Real.log (y : ℝ) - 2 ≤ ∑ p ∈ y.primesLE, Real.log (p : ℝ) / (p : ℝ) :=
    log_sub_two_le_primesLE_log_div y hy
  have hypos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hlogzy : Real.log ((z : ℝ) / (y : ℝ)) = Real.log (z : ℝ) - Real.log (y : ℝ) :=
    Real.log_div (ne_of_gt hzpos) (ne_of_gt hypos)
  have hLnn : 0 ≤ Real.log (z : ℝ) - Real.log (y : ℝ) := by
    have := Real.log_le_log hypos (show (y : ℝ) ≤ (z : ℝ) by exact_mod_cast hyz)
    linarith
  rw [hlogzy]
  have h1 : (∑ p ∈ z.primesLE, Real.log (p : ℝ) / (p : ℝ))
      - (∑ p ∈ y.primesLE, Real.log (p : ℝ) / (p : ℝ))
      ≤ Real.log (z : ℝ) - Real.log (y : ℝ) + 2 := by linarith
  have h2 : C * ((∑ p ∈ z.primesLE, Real.log (p : ℝ) / (p : ℝ))
      - (∑ p ∈ y.primesLE, Real.log (p : ℝ) / (p : ℝ)))
      ≤ C * (Real.log (z : ℝ) - Real.log (y : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left h1 hCnn
  have hCL : 0 ≤ C * (Real.log (z : ℝ) - Real.log (y : ℝ)) := mul_nonneg hCnn hLnn
  have h3 : C * (Real.log (z : ℝ) - Real.log (y : ℝ) + 2)
      ≤ 2 * C * (1 + (Real.log (z : ℝ) - Real.log (y : ℝ))) := by
    nlinarith [hCL, hCpos]
  linarith [h2, h3]

end Commons.NumberTheory.Chebyshev
