import Mathlib.Data.Int.Star
import Submission.Commons.NumberTheory.Int.ncard_int_residue_class_sq_le

namespace Commons.NumberTheory.Int

/-- **Counting the multiples of `k` in `[-Y, Y]`.**  The integers `b` divisible by `k` and
satisfying `|b| ≤ Y` are a subset of the residue class `0` modulo `k` inside `[-Y, Y]`, so
`card_le_of_modEq_abs_le` bounds their number by `2 Y / k + 1`. -/
theorem card_int_multiples_abs_le {k : ℕ} (hk : 1 ≤ k) {Y : ℝ} (hY : 0 ≤ Y) :
    (({b : ℤ | (k : ℤ) ∣ b ∧ |(b : ℝ)| ≤ Y}).ncard : ℝ) ≤ 2 * Y / (k : ℝ) + 1 := by
  classical
  let S : Set ℤ := {b : ℤ | (k : ℤ) ∣ b ∧ |(b : ℝ)| ≤ Y}
  have hsub : S ⊆ (Finset.Icc (-⌊Y⌋) ⌊Y⌋ : Set ℤ) := by
    intro b hb
    obtain ⟨_, habs⟩ := hb
    rw [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · have h1 : ((-b : ℤ) : ℝ) ≤ Y := by
        have h := neg_le_abs (b : ℝ)
        push_cast
        linarith
      have h2 : -b ≤ ⌊Y⌋ := Int.le_floor.mpr h1
      linarith
    · have h1 : (b : ℝ) ≤ Y := le_trans (le_abs_self _) habs
      exact Int.le_floor.mpr h1
  have hSfin : S.Finite := Set.Finite.subset (Finset.finite_toSet _) hsub
  have hcount := card_le_of_modEq_abs_le (d := k) hk (s := hSfin.toFinset) (r := 0) (A := Y) hY
      (fun a ha => Int.modEq_zero_iff_dvd.mpr (hSfin.mem_toFinset.mp ha).1)
      (fun a ha => (hSfin.mem_toFinset.mp ha).2)
  change (S.ncard : ℝ) ≤ 2 * Y / (k : ℝ) + 1
  rw [Set.ncard_eq_toFinset_card S hSfin]
  exact hcount

end Commons.NumberTheory.Int