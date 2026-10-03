import Mathlib
import Submission.Work.FIArea7.logPowBound
import Submission.Work.FIArea7.divisorsSmallPart
import Submission.Work.FIArea7.divisorsLargePart

set_option autoImplicit false

open Finset

namespace Work.FIArea7

/-- **The divisor function is smaller than any fixed power of `n`.**  For every `ε > 0` there is
`n₀` with `τ(n) ≤ n^ε` for `n ≥ n₀` — the elementary bound `τ(n) ≤ ∏_{p^a ‖ n}(a+1)` combined
with `a + 1 ≤ 2^a` and `Ω(n) ≤ log₂ n`, or the sharper `τ(n) ≤ exp(C log n / log log n)`. -/
theorem tauLeRpow (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → (((n.divisors.card : ℕ) : ℝ)) ≤ (n : ℝ) ^ ε := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 / ε)
  set q : ℕ := max N 1 with hq
  have hqpos : 0 < q := by rw [hq]; exact lt_of_lt_of_le one_pos (le_max_right N 1)
  have hqpos' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hqge : 2 / ε ≤ (q : ℝ) := by
    have h2 : ((N : ℕ) : ℝ) ≤ (q : ℝ) := by rw [hq]; exact_mod_cast le_max_left N 1
    linarith
  have hqin : (1 : ℝ) / (q : ℝ) ≤ ε / 2 := by
    have h : (2 : ℝ) ≤ ε * (q : ℝ) := by
      have h2 := (div_le_iff₀ hε).mp hqge
      linarith
    rw [div_le_div_iff₀ hqpos' (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hd : 0 < ε - 1 / (q : ℝ) := by linarith
  obtain ⟨N₁, hN₁⟩ := logPowBound (ε - 1 / (q : ℝ)) hd (2 ^ q)
  refine ⟨max N₁ 2, ?_⟩
  intro n hn
  have h2le : 2 ≤ n := le_trans (le_max_right N₁ 2) hn
  have hn0 : n ≠ 0 := by omega
  have hN1n : N₁ ≤ n := le_trans (le_max_left N₁ 2) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcard : ((n.divisors.card : ℕ) : ℝ)
      = ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
    rw [Nat.card_divisors hn0, Nat.cast_prod]
  have hsplit := Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p < 2 ^ q)
      (fun p => ((n.factorization p + 1 : ℕ) : ℝ))
  rw [hcard, ← hsplit]
  have hsmall : (∏ p ∈ n.primeFactors.filter (fun p => p < 2 ^ q),
        ((n.factorization p + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ (ε - 1 / (q : ℝ)) :=
    le_trans (divisorsSmallPart (2 ^ q) n) (hN₁ n hN1n)
  have hlarge : (∏ p ∈ n.primeFactors.filter (fun p => ¬ p < 2 ^ q),
        ((n.factorization p + 1 : ℕ) : ℝ)) ≤ (n : ℝ) ^ ((1 : ℝ) / (q : ℝ)) := by
    have h := divisorsLargePart q n hn0
    have heq : n.primeFactors.filter (fun p => 2 ^ q ≤ p)
        = n.primeFactors.filter (fun p => ¬ p < 2 ^ q) := by
      ext p; simp only [Finset.mem_filter, not_lt]
    rw [heq] at h
    have hXnn : 0 ≤ ∏ p ∈ n.primeFactors.filter (fun p => ¬ p < 2 ^ q),
        ((n.factorization p + 1 : ℕ) : ℝ) := Finset.prod_nonneg (fun p hp => by positivity)
    have hqnn : 0 ≤ (1 : ℝ) / (q : ℝ) := by positivity
    have hstep : ((∏ p ∈ n.primeFactors.filter (fun p => ¬ p < 2 ^ q),
          ((n.factorization p + 1 : ℕ) : ℝ)) ^ ((q : ℝ))) ^ ((1 : ℝ) / (q : ℝ))
        ≤ (n : ℝ) ^ ((1 : ℝ) / (q : ℝ)) := by
      apply Real.rpow_le_rpow (Real.rpow_nonneg hXnn _)
      · rw [Real.rpow_natCast]; exact h
      · exact hqnn
    have hsimp : ((∏ p ∈ n.primeFactors.filter (fun p => ¬ p < 2 ^ q),
          ((n.factorization p + 1 : ℕ) : ℝ)) ^ ((q : ℝ))) ^ ((1 : ℝ) / (q : ℝ))
        = ∏ p ∈ n.primeFactors.filter (fun p => ¬ p < 2 ^ q),
          ((n.factorization p + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_mul hXnn,
        show (q : ℝ) * ((1 : ℝ) / (q : ℝ)) = 1 by rw [one_div, mul_inv_cancel₀ (ne_of_gt hqpos')],
        Real.rpow_one]
    rwa [hsimp] at hstep
  calc (∏ p ∈ n.primeFactors.filter (fun p => p < 2 ^ q), ((n.factorization p + 1 : ℕ) : ℝ))
        * (∏ p ∈ n.primeFactors.filter (fun p => ¬ p < 2 ^ q),
            ((n.factorization p + 1 : ℕ) : ℝ))
      ≤ (n : ℝ) ^ (ε - 1 / (q : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / (q : ℝ)) :=
        mul_le_mul hsmall hlarge (Finset.prod_nonneg (fun p hp => by positivity))
          (Real.rpow_nonneg (by positivity) _)
    _ = (n : ℝ) ^ ε := by
        have h1 : (n : ℝ) ^ (ε - 1 / (q : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / (q : ℝ))
            = (n : ℝ) ^ ((ε - 1 / (q : ℝ)) + (1 : ℝ) / (q : ℝ)) :=
          (Real.rpow_add hnpos _ _).symm
        rw [h1, show (ε - 1 / (q : ℝ)) + (1 : ℝ) / (q : ℝ) = ε by ring]

end Work.FIArea7
