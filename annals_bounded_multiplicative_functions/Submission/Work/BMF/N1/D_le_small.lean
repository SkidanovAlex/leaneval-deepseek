import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N1

open Polynomial Finset Real Complex BoundedMultiplicativeFunctions
open scoped ComplexConjugate
open Work.BMF

/-- Crude bound for `𝔻` at a scale `Y` below a known upper bound `Z`: each summand is at most
`2/p` and there are at most `⌊Z⌋₊` primes, so `𝔻 f g Y ≤ √(2 (Z+1))`. -/
theorem D_le_small {f g : ℕ → ℂ} (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Y Z : ℝ} (hYZ : Y ≤ Z) (hZ : 0 ≤ Z) : 𝔻 f g Y ≤ Real.sqrt (2 * (Z + 1)) := by
  rw [𝔻, ← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_sqrt
  -- Each summand is at most `1`: the numerator `1 - Re(f p · conj (g p))` lies in `[0, 2]`,
  -- and `2 ≤ p`.
  have hterm : ∀ p ∈ (⌊Y⌋₊).primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ) ≤ (1 : ℝ) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hnorm : ‖f p * conj (g p)‖ ≤ 1 := by
      rw [norm_mul, norm_conj]
      nlinarith [hf p hpp, hg p hpp, norm_nonneg (f p), norm_nonneg (g p)]
    have habs : |(f p * conj (g p)).re| ≤ 1 := (Complex.abs_re_le_norm _).trans hnorm
    have hle2 : 1 - (f p * conj (g p)).re ≤ 2 := by
      have := (abs_le.mp habs).1; linarith
    rw [div_le_one (by linarith)]
    linarith
  -- The sum is bounded by the number of summands.
  have hsum : ∑ p ∈ (⌊Y⌋₊).primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)
      ≤ (((⌊Y⌋₊).primesLE).card : ℝ) := by
    calc ∑ p ∈ (⌊Y⌋₊).primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)
        ≤ ∑ p ∈ (⌊Y⌋₊).primesLE, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (((⌊Y⌋₊).primesLE).card : ℝ) := by simp
  -- The number of primes up to `⌊Y⌋₊` is at most `⌊Y⌋₊ + 1 ≤ Z + 1`.
  have hcard : (((⌊Y⌋₊).primesLE).card : ℝ) ≤ Z + 1 := by
    have h1 : ((⌊Y⌋₊).primesLE).card ≤ ⌊Y⌋₊ + 1 := by
      rw [Nat.primesLE_eq_filter_range]
      calc (Finset.filter Nat.Prime (Finset.range (⌊Y⌋₊ + 1))).card
          ≤ (Finset.range (⌊Y⌋₊ + 1)).card := Finset.card_filter_le _ _
        _ = ⌊Y⌋₊ + 1 := Finset.card_range _
    have h2 : ((⌊Y⌋₊ : ℝ) + 1) ≤ Z + 1 := by
      rcases lt_or_ge 0 Y with hY | hY
      · have h0 : 0 ≤ Y := le_of_lt hY
        have := Nat.floor_le h0; linarith
      · have : ⌊Y⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        rw [this]; push_cast; linarith
    have h3 : (((⌊Y⌋₊ + 1 : ℕ)) : ℝ) = (⌊Y⌋₊ : ℝ) + 1 := by push_cast; ring
    have h4 : (((⌊Y⌋₊).primesLE).card : ℝ) ≤ (((⌊Y⌋₊ + 1 : ℕ)) : ℝ) := by
      exact_mod_cast h1
    linarith
  have h4 : Z + 1 ≤ 2 * (Z + 1) := by linarith
  linarith

end Work.BMF.N1
