import Mathlib
import Submission.Work.BMF.mr_direct.primePolyWindow_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Sums of `1/p` and `1/p^2` over a prime window `[A, B]`, `A ≤ B ≤ 4A`

For `A ≥ 2` and `A ≤ B ≤ 4 A` the window `[⌈A⌉₊, ⌊B⌋₊]` contains at most `⌊B⌋₊ + 1 ≤ 4A + 1`
primes, and every prime in it is at least `A`.  Hence the very crude bounds

* `Σ_p 1/p ≤ (4A+1)/A ≤ 5`,
* `Σ_p 1/p² ≤ (4A+1)/A² ≤ 5/A`

(the last because `A ≥ 1`), which is all that the proof of the mean value theorem for the
prime Dirichlet polynomial on a general window `[A, B]` needs.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open Finset
open scoped BigOperators

lemma winSet_inv_sums (A B : ℝ) (hA : 2 ≤ A) (hAB : A ≤ B) (hB : B ≤ 4 * A) :
    (∑ p ∈ Work.BMF.mr_direct.primePolyWindow.winSet A B, (1 : ℝ) / (p : ℝ)) ≤ 5 ∧
      (∑ p ∈ Work.BMF.mr_direct.primePolyWindow.winSet A B, (1 : ℝ) / (p : ℝ) ^ 2)
        ≤ 5 / A := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hfloor : (⌊B⌋₊ : ℝ) ≤ 4 * A := le_trans (Nat.floor_le hB0) hB
  -- the window contains at most `⌊B⌋₊ + 1` primes
  have hcardN : (primePolyWindow.winSet A B).card ≤ ⌊B⌋₊ + 1 := by
    have hsub : primePolyWindow.winSet A B ⊆ Finset.range (⌊B⌋₊ + 1) := by
      intro p hp
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (primePolyWindow.mem_winSet hp).2.2
    calc (primePolyWindow.winSet A B).card
        ≤ (Finset.range (⌊B⌋₊ + 1)).card := Finset.card_le_card hsub
      _ = ⌊B⌋₊ + 1 := Finset.card_range _
  have hcard : ((primePolyWindow.winSet A B).card : ℝ) ≤ 4 * A + 1 := by
    have h1 : ((⌊B⌋₊ + 1 : ℕ) : ℝ) = (⌊B⌋₊ : ℝ) + 1 := by push_cast; ring
    have h2 : ((primePolyWindow.winSet A B).card : ℝ) ≤ ((⌊B⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcardN
    rw [h1] at h2
    linarith
  -- every prime in the window is at least `A`
  have hterm : ∀ p ∈ primePolyWindow.winSet A B, A ≤ (p : ℝ) := by
    intro p hp
    have hpge : ⌈A⌉₊ ≤ p := (primePolyWindow.mem_winSet hp).2.1
    have h1 : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    have h2 : ((⌈A⌉₊ : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpge
    linarith
  constructor
  · have hsum : (∑ p ∈ primePolyWindow.winSet A B, (1 : ℝ) / (p : ℝ))
        ≤ ((primePolyWindow.winSet A B).card : ℝ) * (1 / A) := by
      calc (∑ p ∈ primePolyWindow.winSet A B, (1 : ℝ) / (p : ℝ))
          ≤ ∑ p ∈ primePolyWindow.winSet A B, (1 / A) :=
            Finset.sum_le_sum (fun p hp => one_div_le_one_div_of_le hA0 (hterm p hp))
        _ = ((primePolyWindow.winSet A B).card : ℝ) * (1 / A) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hstep : ((primePolyWindow.winSet A B).card : ℝ) * (1 / A) ≤ (4 * A + 1) * (1 / A) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have hfin : (4 * A + 1) * (1 / A) ≤ 5 := by
      rw [mul_one_div, div_le_iff₀ hA0]
      linarith
    linarith
  · have hterm2 : ∀ p ∈ primePolyWindow.winSet A B, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / A ^ 2 := by
      intro p hp
      refine one_div_le_one_div_of_le (by positivity) ?_
      nlinarith [hterm p hp, hA0]
    have hsum : (∑ p ∈ primePolyWindow.winSet A B, (1 : ℝ) / (p : ℝ) ^ 2)
        ≤ ((primePolyWindow.winSet A B).card : ℝ) * (1 / A ^ 2) := by
      calc (∑ p ∈ primePolyWindow.winSet A B, (1 : ℝ) / (p : ℝ) ^ 2)
          ≤ ∑ p ∈ primePolyWindow.winSet A B, (1 / A ^ 2) :=
            Finset.sum_le_sum (fun p hp => hterm2 p hp)
        _ = ((primePolyWindow.winSet A B).card : ℝ) * (1 / A ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hstep : ((primePolyWindow.winSet A B).card : ℝ) * (1 / A ^ 2)
        ≤ (4 * A + 1) * (1 / A ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have hfin : (4 * A + 1) * (1 / A ^ 2) ≤ 5 / A := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) hA0]
      nlinarith
    linarith

end Work.BMF.mr_direct
