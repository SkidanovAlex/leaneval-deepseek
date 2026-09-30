import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- Crude bound for the sum of `1/p` over the primes `p ∈ [l, u]`: since every such prime
satisfies `p ≥ l`, each term is at most `1/l`, and there are at most `u + 1 - l` of them
(distinct integers in `[l, u]`). -/
lemma sum_inv_primes_le (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) :
    ∑ p ∈ Work.BMF.primesIn l u, (1 : ℝ) / (p : ℝ) ≤ (u + 1 - l) / l := by
  -- each term is at most `1/l`
  have hterm : ∀ p ∈ Work.BMF.primesIn l u, (1 : ℝ) / (p : ℝ) ≤ 1 / l := by
    intro p hp
    have hmem : ⌈l⌉₊ ≤ p ∧ p ≤ ⌊u⌋₊ := by
      have h := hp
      simp only [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc] at h
      exact h.1
    have hpl : l ≤ (p : ℝ) := by
      have h2 : (⌈l⌉₊ : ℝ) ≤ (p : ℝ) := by exact_mod_cast hmem.1
      have h3 : l ≤ (⌈l⌉₊ : ℝ) := Nat.le_ceil l
      linarith
    exact one_div_le_one_div_of_le hl hpl
  -- the number of primes is at most `u + 1 - l`
  have hcard : ((Work.BMF.primesIn l u).card : ℝ) ≤ u + 1 - l := by
    have hsub : Work.BMF.primesIn l u ⊆ Finset.Icc ⌈l⌉₊ ⌊u⌋₊ := by
      intro p hp
      have hmem : ⌈l⌉₊ ≤ p ∧ p ≤ ⌊u⌋₊ := by
        have h := hp
        simp only [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc] at h
        exact h.1
      exact Finset.mem_Icc.mpr hmem
    have h1 : (Work.BMF.primesIn l u).card ≤ (Finset.Icc ⌈l⌉₊ ⌊u⌋₊).card :=
      Finset.card_le_card hsub
    rw [Nat.card_Icc] at h1
    have hbu : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (le_trans hl.le hlu)
    have hal : l ≤ (⌈l⌉₊ : ℝ) := Nat.le_ceil l
    by_cases hc : ⌈l⌉₊ ≤ ⌊u⌋₊ + 1
    · have h2 : ((⌊u⌋₊ + 1 - ⌈l⌉₊ : ℕ) : ℝ) = (⌊u⌋₊ : ℝ) + 1 - (⌈l⌉₊ : ℝ) := by
        rw [Nat.cast_sub hc]; push_cast; ring
      calc ((Work.BMF.primesIn l u).card : ℝ)
          ≤ ((⌊u⌋₊ + 1 - ⌈l⌉₊ : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (⌊u⌋₊ : ℝ) + 1 - (⌈l⌉₊ : ℝ) := h2
        _ ≤ u + 1 - l := by linarith
    · push Not at hc
      have hzero : ⌊u⌋₊ + 1 - ⌈l⌉₊ = 0 := by omega
      rw [hzero] at h1
      have hz : (Work.BMF.primesIn l u).card = 0 := by omega
      rw [hz]
      push_cast
      linarith
  calc ∑ p ∈ Work.BMF.primesIn l u, (1 : ℝ) / (p : ℝ)
      ≤ ∑ _p ∈ Work.BMF.primesIn l u, 1 / l := Finset.sum_le_sum hterm
    _ = ((Work.BMF.primesIn l u).card : ℝ) * (1 / l) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (u + 1 - l) * (1 / l) := by
        apply mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (u + 1 - l) / l := by ring

end Work.BMF.mr_direct
