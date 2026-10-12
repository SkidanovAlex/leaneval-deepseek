import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseB7AK.K15R.card_le_of_vec_norm_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.K15R.small_part_scaled` — the small-ball part of the lattice sum

The box momenta are the dual-lattice points `vec n = 2πn` (`Work.BoseB4.vec`), so
`‖vec n‖ < ℓ` says `n` lies in the ball of radius `ℓ`.  On that ball

* every summand is at most `1`, because `1 + ‖vec n‖/ℓ ≥ 1` and the exponent
  `-4` is nonpositive;
* the ball meets `ℤ³` in at most `(ℓ/π+1)³ ≤ (2ℓ)³ = 8ℓ³` points
  (`Work.BoseB7AK.K15R.card_le_of_vec_norm_le`).

Hence the truncated sum is at most `8ℓ³`.  This is the piece of the ball/tail
split of `Work.BoseB7AK.K15R.lattice_sum_scaled`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7AK.K15R

theorem small_part_scaled (ℓ : ℝ) (hℓ : 1 ≤ ℓ) (T : Finset (Fin 3 → ℤ))
    (hT : ∀ n ∈ T, ‖Work.BoseB4.vec n‖ < ℓ) :
    (∑ n ∈ T, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ))) ≤ 8 * ℓ ^ 3 := by
  have hℓpos : 0 < ℓ := lt_of_lt_of_le one_pos hℓ
  -- every summand is at most `1`
  have hterm : ∀ n ∈ T, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)) ≤ 1 := by
    intro n _
    have hb : (1 : ℝ) ≤ 1 + ‖Work.BoseB4.vec n‖ / ℓ := by
      have : 0 ≤ ‖Work.BoseB4.vec n‖ / ℓ := div_nonneg (norm_nonneg _) (le_of_lt hℓpos)
      linarith
    calc (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ))
        ≤ (1 : ℝ) ^ (-(4 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos one_pos hb (by norm_num)
      _ = 1 := Real.one_rpow _
  -- hence the sum is at most the cardinality of the set
  have hsum : (∑ n ∈ T, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ))) ≤ (T.card : ℝ) := by
    calc (∑ n ∈ T, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)))
        ≤ ∑ n ∈ T, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (T.card : ℝ) := by simp
  -- the ball of radius `ℓ` meets `ℤ³` in at most `(ℓ/π+1)³` points
  have hcard : (T.card : ℝ) ≤ (ℓ / Real.pi + 1) ^ 3 :=
    card_le_of_vec_norm_le T ℓ (le_of_lt hℓpos) (fun n hn => le_of_lt (hT n hn))
  -- and `(ℓ/π+1)³ ≤ (2ℓ)³ = 8ℓ³`
  have hcube : (ℓ / Real.pi + 1) ^ 3 ≤ 8 * ℓ ^ 3 := by
    have hbase : ℓ / Real.pi + 1 ≤ 2 * ℓ := by
      have h1 : ℓ / Real.pi ≤ ℓ := by
        rw [div_le_iff₀ Real.pi_pos]
        nlinarith [Real.pi_gt_three, hℓ]
      linarith
    have h2 : (ℓ / Real.pi + 1) ^ 3 ≤ (2 * ℓ) ^ 3 := pow_le_pow_left₀ (by positivity) hbase 3
    nlinarith [h2]
  calc (∑ n ∈ T, (1 + ‖Work.BoseB4.vec n‖ / ℓ) ^ (-(4 : ℝ)))
      ≤ (T.card : ℝ) := hsum
    _ ≤ (ℓ / Real.pi + 1) ^ 3 := hcard
    _ ≤ 8 * ℓ ^ 3 := hcube

end Work.BoseB7AK.K15R
