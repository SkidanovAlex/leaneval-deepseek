import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs

namespace Work.KMTAreas.A4

/-- For every positive real `r` there is a power of two inside `[r, 2 * max r 1]`:
the least power of two which is at least `r` overshoots `r` by at most a factor `2`
(and if `r ≤ 1` the zeroth power does the job).
This is the elementary "choose the scale" lemma of the `LIP` step of Area A4. -/
theorem lipExistsPowTwoGe {r : ℝ} (hr : 0 < r) :
    ∃ l : ℕ, r ≤ (2 : ℝ) ^ l ∧ (2 : ℝ) ^ l ≤ 2 * max r 1 := by
  -- some power of two is at least `r`
  have hex : ∃ l : ℕ, r ≤ (2 : ℝ) ^ l := by
    obtain ⟨n, hn⟩ := exists_nat_ge r
    refine ⟨n, le_trans hn ?_⟩
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  by_cases h0 : Nat.find hex = 0
  · -- `r ≤ 1` and the zeroth power works
    have hone : (2 : ℝ) ^ Nat.find hex = 1 := by rw [h0]; norm_num
    rw [hone]
    have hmax : (1 : ℝ) ≤ max r 1 := le_max_right r 1
    linarith
  · -- the least admissible power has index `m + 1 ≥ 1`, and minimality gives `2 ^ m < r`
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hlt : m < Nat.find hex := by omega
    have hmin : ¬ r ≤ (2 : ℝ) ^ m := Nat.find_min hex hlt
    have hmr : (2 : ℝ) ^ m < max r 1 :=
      lt_of_lt_of_le (lt_of_not_ge hmin) (le_max_left r 1)
    have hpow : (2 : ℝ) ^ Nat.find hex = 2 * (2 : ℝ) ^ m := by
      rw [hm, pow_succ]; ring
    rw [hpow]
    linarith

end Work.KMTAreas.A4
