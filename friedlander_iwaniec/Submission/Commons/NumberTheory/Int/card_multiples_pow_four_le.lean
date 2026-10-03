import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.NumberTheory.Int.card_int_multiples_abs_le
import Submission.Commons.NumberTheory.Int.int_pow_four_le_iff_abs_le_sqrt

namespace Commons.NumberTheory.Int

/-- If an integer `b` satisfies `b ^ 4 ≤ x` then `|b| ≤ x^{1/4}`.  This is the lemmas
`int_pow_four_le_iff_abs_le_sqrt` (for `1 ≤ x`) together with the trivial case `x = 0`. -/
lemma pow_four_le_abs_le_sqrt (x : ℕ) (b : ℤ) (h : b ^ 4 ≤ (x : ℤ)) :
    |(b : ℝ)| ≤ Real.sqrt (Real.sqrt (x : ℝ)) := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    have hz : b ^ 4 = 0 := le_antisymm h (by positivity)
    have hb : b = 0 := (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hz
    subst hb
    simp
  · exact (int_pow_four_le_iff_abs_le_sqrt x hx b).mp h

/-- **Counting the integers `b` with `b ^ 4 ≤ x` that are divisible by `k`.**

All such `b` lie in `[-x^{1/4}, x^{1/4}]`, so they form a set of multiples of `k` inside a ball of
radius `x^{1/4}`; `card_int_multiples_abs_le` bounds the latter by `2 x^{1/4}/k + 1`. -/
theorem card_multiples_pow_four_le (x k : ℕ) (hk : 1 ≤ k) :
    ((((Finset.Icc (-(x : ℤ)) x).filter (fun b => b ^ 4 ≤ (x : ℤ))).filter
        (fun b => (k : ℤ) ∣ b)).card : ℝ)
      ≤ 2 * Real.sqrt (Real.sqrt (x : ℝ)) / (k : ℝ) + 1 := by
  classical
  let Y : ℝ := Real.sqrt (Real.sqrt (x : ℝ))
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  let S : Finset ℤ := ((Finset.Icc (-(x : ℤ)) (x : ℤ)).filter
      (fun b => b ^ 4 ≤ (x : ℤ))).filter (fun b => (k : ℤ) ∣ b)
  change (S.card : ℝ) ≤ 2 * Real.sqrt (Real.sqrt (x : ℝ)) / (k : ℝ) + 1
  have hsub : (S : Set ℤ) ⊆ {b : ℤ | (k : ℤ) ∣ b ∧ |(b : ℝ)| ≤ Y} := by
    intro b hb
    simp only [S, Finset.mem_coe, Finset.mem_filter] at hb
    exact ⟨hb.2, pow_four_le_abs_le_sqrt x b hb.1.2⟩
  have hfin : ({b : ℤ | (k : ℤ) ∣ b ∧ |(b : ℝ)| ≤ Y}).Finite := by
    apply Set.Finite.subset
      (Finset.finite_toSet (Finset.Icc (-⌊Y⌋) ⌊Y⌋))
    intro b hb
    obtain ⟨_, habs⟩ := hb
    rw [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · have h1 : ((-b : ℤ) : ℝ) ≤ Y := by
        have := neg_le_abs (b : ℝ); push_cast; linarith
      have h2 := Int.le_floor.mpr h1
      linarith
    · exact Int.le_floor.mpr (le_trans (le_abs_self _) habs)
  have hcard : (S.card : ℝ) ≤ (({b : ℤ | (k : ℤ) ∣ b ∧ |(b : ℝ)| ≤ Y}).ncard : ℝ) := by
    rw [← Set.ncard_coe_finset S]
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  calc (S.card : ℝ)
      ≤ (({b : ℤ | (k : ℤ) ∣ b ∧ |(b : ℝ)| ≤ Y}).ncard : ℝ) := hcard
    _ ≤ 2 * Y / (k : ℝ) + 1 := card_int_multiples_abs_le hk hY
    _ = 2 * Real.sqrt (Real.sqrt (x : ℝ)) / (k : ℝ) + 1 := by rfl

end Commons.NumberTheory.Int