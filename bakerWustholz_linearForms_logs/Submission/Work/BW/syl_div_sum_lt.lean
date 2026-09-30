import Mathlib
import Submission.Work.BW.ulcm_le_three_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The Egyptian-fraction identity for the Sylvester sequence, over `ℝ`:
`∑_{i<k} 1/syl i = 1 - 1/(syl k - 1)`.  (Local copy, to keep this file's imports light.) -/
private lemma syl_sum_inv_real_aux' (m : ℕ) :
    (∑ i ∈ Finset.range m, (1 : ℝ) / (syl i : ℝ)) = 1 - 1 / ((syl m : ℝ) - 1) := by
  induction m with
  | zero => norm_num [syl_zero]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : 2 ≤ syl m := syl_two_le m
      have hcast : ((syl (m + 1) : ℕ) : ℝ) - 1 = (syl m : ℝ) * ((syl m : ℝ) - 1) := by
        rw [syl_succ]
        push_cast [Nat.cast_sub (show 1 ≤ syl m by omega)]
        ring
      have hsm : (syl m : ℝ) ≠ 0 := by
        have h : (0 : ℝ) < (syl m : ℝ) := by exact_mod_cast (by omega : 0 < syl m)
        linarith
      have hne : (syl m : ℝ) - 1 ≠ 0 := by
        have h3 : (2 : ℝ) ≤ (syl m : ℝ) := by exact_mod_cast h2
        intro h; linarith
      rw [hcast]
      field_simp
      ring

/-- **Reciprocal Sylvester sum, real-division form.**  For `n ≥ 1`,
`∑_{i ≤ n} n / syl i < n` (real division), with `syl` Sylvester's sequence from
`Submission/Work/BW/ulcm_le_three_pow.lean`.  This is the `∑_i n/syl i - n < 0` input of the
entropy bound for `n!/sylBlocks n`.

Route.  `∑_{i≤n} n/syl i = n * ∑_{i≤n} 1/syl i` (`Finset.mul_sum`), and the Egyptian-fraction
identity `∑_{i<k} 1/syl i = 1 - 1/(syl k - 1)` (`Work.BW.syl_sum_inv`, over `ℚ`; cast it to `ℝ` or
redo the induction in `ℝ`, cf. `Work.BW.syl_sum_inv_real_aux`) at `k = n+1` gives
`∑_{i≤n} 1/syl i = 1 - 1/(syl (n+1) - 1) < 1` since `syl (n+1) - 1 > 0` (`syl_two_le`).  Multiply
by `n > 0`. -/
theorem syl_div_sum_lt (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (n + 1), (n : ℝ) / (syl i : ℝ)) < (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsplit : (∑ i ∈ Finset.range (n + 1), (n : ℝ) / (syl i : ℝ))
      = (n : ℝ) * (∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (syl i : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_one_div]
  rw [hsplit, syl_sum_inv_real_aux' (n + 1)]
  have hpos : (0 : ℝ) < (syl (n + 1) : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ (syl (n + 1) : ℝ) := by exact_mod_cast syl_two_le (n + 1)
    linarith
  have hinv : (0 : ℝ) < 1 / ((syl (n + 1) : ℝ) - 1) := one_div_pos.mpr hpos
  nlinarith [mul_pos hnR hinv]

end Work.BW
