import Mathlib

/-!
# A real-power estimate for the `v2` master inequality

`Work.WilkiesH.Interp.V2master.rpow_pow_add_two_le`: for `r ≥ 1` and `μ : ℕ`,
`(r^(μ+1) + 2)^(μ/(μ+1)) ≤ 3 r^μ`.

The proof: with `b := r^(μ+1) ≥ 1` one has `b + 2 ≤ 3b`, hence
`(b+2)^s ≤ (3b)^s = 3^s b^s` for `s = μ/(μ+1) ≥ 0`; moreover
`b^s = r^((μ+1)·s) = r^μ` and `3^s ≤ 3` (as `s ≤ 1`).
-/

set_option maxHeartbeats 1000000

namespace Work.WilkiesH.Interp.V2master

lemma rpow_pow_add_two_le (μ : ℕ) (r : ℝ) (hr : 1 ≤ r) :
    (r ^ (μ + 1) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) ≤ 3 * r ^ μ := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hmu1 : (0 : ℝ) < (μ : ℝ) + 1 := by positivity
  have hs0 : (0 : ℝ) ≤ (μ : ℝ) / ((μ : ℝ) + 1) := div_nonneg (Nat.cast_nonneg μ) (le_of_lt hmu1)
  have hs1 : (μ : ℝ) / ((μ : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hmu1]; linarith
  -- the exponent identity `((μ:ℝ)+1) * (μ/((μ:ℝ)+1)) = μ`
  have hexp : ((μ : ℝ) + 1) * ((μ : ℝ) / ((μ : ℝ) + 1)) = (μ : ℝ) := by
    field_simp
  -- rewrite the statement in the `rpow` form
  have hbase : (r ^ (μ + 1) : ℝ) = r ^ ((μ : ℝ) + 1) := by
    rw [← Real.rpow_natCast r (μ + 1)]
    push_cast
    ring
  rw [hbase, ← Real.rpow_natCast r μ]
  -- the core estimate, entirely in `rpow`
  have hb1 : (1 : ℝ) ≤ r ^ ((μ : ℝ) + 1) := Real.one_le_rpow hr (by linarith)
  have hb0 : (0 : ℝ) ≤ r ^ ((μ : ℝ) + 1) := le_trans zero_le_one hb1
  have hle : r ^ ((μ : ℝ) + 1) + 2 ≤ 3 * r ^ ((μ : ℝ) + 1) := by linarith
  calc (r ^ ((μ : ℝ) + 1) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1))
      ≤ (3 * r ^ ((μ : ℝ) + 1)) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) :=
        Real.rpow_le_rpow (by linarith) hle hs0
    _ = 3 ^ ((μ : ℝ) / ((μ : ℝ) + 1)) *
          (r ^ ((μ : ℝ) + 1)) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) :=
        Real.mul_rpow (by norm_num) hb0
    _ = 3 ^ ((μ : ℝ) / ((μ : ℝ) + 1)) * r ^ (μ : ℝ) := by
        rw [← Real.rpow_mul (le_of_lt hr0) ((μ : ℝ) + 1) ((μ : ℝ) / ((μ : ℝ) + 1)), hexp]
    _ ≤ 3 * r ^ (μ : ℝ) := by
        have h3 : (3 : ℝ) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) ≤ 3 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hs1
        exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (le_of_lt hr0) _)

end Work.WilkiesH.Interp.V2master
