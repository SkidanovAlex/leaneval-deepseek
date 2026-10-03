/-
# `Work.FIChain.FIgtil_prime_le_third`

At a prime `p` the FI modified density satisfies `g̃(p) ≤ 1/3`, where
`g̃ = Submission.ASP.FIgtil` and `g̃(p) = (g(p) − g(p²))/(1 − g(p²))`.
The bound is sharp: `g̃(2) = 1/3` exactly.

The arithmetic content is the single inequality `3 g(p) − 2 g(p²) ≤ 1`, which is equivalent to
the ratio bound `(g(p) − g(p²))/(1 − g(p²)) ≤ 1/3` because the denominator `1 − g(p²)` is positive.
The three cases:

* `p = 2`: `g(2) = 1/2`, `g(4) = 1/4`, so `3·(1/2) − 2·(1/4) = 1`;
* `p ≡ 1 (mod 4)`: `p² g(p) = 2p − 1` and `p³ g(p²) = 3p − 2`, hence
  `p³(3g(p) − 2g(p²)) = 6p² − 9p + 4 = p³ − (p−1)²(p−4) ≤ p³` as `p ≥ 5`;
* `p ≡ 3 (mod 4)`: `p² g(p) = p² g(p²) = 1`, so `3g(p) − 2g(p²) = 1/p² ≤ 1`.
-/
import Mathlib
import Submission.ASP.S27
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le
import Submission.Work.FIChain.PerLayerDefs

namespace Work.FIChain

open Finset

noncomputable section

/-- For a prime `p`, `3 g(p) − 2 g(p²) ≤ 1`, where `g = Submission.gdens` is the local density of
the Friedlander–Iwaniec sequence.  See the file header for the case analysis. -/
lemma gdens_three_sub_two_le_one {p : ℕ} (hp : p.Prime) :
    3 * Submission.gdens p - 2 * Submission.gdens (p ^ 2) ≤ 1 := by
  by_cases h2 : p = 2
  · subst h2
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, Submission.gdens_four]
    rw [Submission.gdens, Submission.N_prime_two]
    norm_num
  · have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2)
    have hp2 : 2 ≤ p := hp.two_le
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rcases Nat.odd_mod_four_iff.mp hodd with h1 | h3
    · -- `p ≡ 1 (mod 4)`
      have hχ : Submission.chi4 p = 1 := Submission.chi4_one_mod_four h1
      have hA := Submission.gdens_prime_mul hp h2
      have hB := Submission.gdens_prime_sq_mul hp h2
      rw [hχ] at hA hB
      have h5 : (5 : ℚ) ≤ p := by
        have h5n : 5 ≤ p := by omega
        exact_mod_cast h5n
      have hA2 : Submission.gdens p * (p : ℚ) ^ 2 = 2 * (p : ℚ) - 1 := by
        field_simp at hA
        ring_nf at hA ⊢
        linarith [hA]
      have hB3 : Submission.gdens (p ^ 2) * (p : ℚ) ^ 3 = 3 * (p : ℚ) - 2 := by
        field_simp at hB
        ring_nf at hB ⊢
        linarith [hB]
      have hkey : (3 * Submission.gdens p - 2 * Submission.gdens (p ^ 2)) * (p : ℚ) ^ 3
          = 6 * (p : ℚ) ^ 2 - 9 * (p : ℚ) + 4 := by
        nlinarith [hA2, hB3]
      have hsmall : 6 * (p : ℚ) ^ 2 - 9 * (p : ℚ) + 4 ≤ (p : ℚ) ^ 3 := by
        nlinarith [sq_nonneg ((p : ℚ) - 1), h5]
      have hpos : (0 : ℚ) < (p : ℚ) ^ 3 := by positivity
      have hle : (3 * Submission.gdens p - 2 * Submission.gdens (p ^ 2)) * (p : ℚ) ^ 3
          ≤ (1 : ℚ) * (p : ℚ) ^ 3 := by
        rw [hkey]
        simpa using hsmall
      exact (mul_le_mul_iff_left₀ hpos).mp hle
    · -- `p ≡ 3 (mod 4)`
      have hχ : Submission.chi4 p = -1 := Submission.chi4_three_mod_four h3
      have hA := Submission.gdens_prime_mul hp h2
      have hB := Submission.gdens_prime_sq_mul hp h2
      rw [hχ] at hA hB
      have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_le
      have hA2 : Submission.gdens p * (p : ℚ) ^ 2 = 1 := by
        field_simp at hA
        ring_nf at hA ⊢
        linarith [hA]
      have hB3 : Submission.gdens (p ^ 2) * (p : ℚ) ^ 3 = (p : ℚ) := by
        field_simp at hB
        ring_nf at hB ⊢
        linarith [hB]
      have hB2 : Submission.gdens (p ^ 2) * (p : ℚ) ^ 2 = 1 := by
        have hmul : Submission.gdens (p ^ 2) * (p : ℚ) ^ 2 * (p : ℚ) = 1 * (p : ℚ) := by
          rw [mul_assoc, show (p : ℚ) ^ 2 * (p : ℚ) = (p : ℚ) ^ 3 by ring, hB3]
          ring
        exact mul_right_cancel₀ hp0 hmul
      have hkey : (3 * Submission.gdens p - 2 * Submission.gdens (p ^ 2)) * (p : ℚ) ^ 2
          = 1 := by
        nlinarith [hA2, hB2]
      have hge : (1 : ℚ) ≤ (p : ℚ) ^ 2 := by
        nlinarith [sq_nonneg ((p : ℚ) - 1), hp1]
      have hpos : (0 : ℚ) < (p : ℚ) ^ 2 := by positivity
      have hle : (3 * Submission.gdens p - 2 * Submission.gdens (p ^ 2)) * (p : ℚ) ^ 2
          ≤ (1 : ℚ) * (p : ℚ) ^ 2 := by
        rw [hkey]
        simpa using hge
      exact (mul_le_mul_iff_left₀ hpos).mp hle

theorem FIgtil_prime_le_third (p : ℕ) (hp : p.Prime) : Submission.ASP.FIgtil p ≤ 1 / 3 := by
  have hnum : (3 : ℝ) * Submission.ASP.FIg p - 2 * Submission.ASP.FIg (p ^ 2) ≤ 1 := by
    simp only [Submission.ASP.FIg]
    exact_mod_cast gdens_three_sub_two_le_one hp
  have hden : (0 : ℝ) < 1 - Submission.ASP.FIg (p ^ 2) := by
    have hlt : Submission.gdens (p ^ 2) < 1 :=
      lt_of_le_of_lt (Submission.gdens_prime_sq_le hp) (Submission.gdens_prime_lt_one hp)
    have hltR : ((Submission.gdens (p ^ 2) : ℚ) : ℝ) < 1 := by exact_mod_cast hlt
    simp only [Submission.ASP.FIg]
    linarith
  rw [Submission.ASP.FIgtil_prime hp]
  simp only [Submission.ASP.gtilVal]
  rw [div_le_iff₀ hden]
  linarith [hnum]

end

end Work.FIChain
