import Mathlib

/-!
# A Chebyshev-type upper bound: `π(w) · log w ≪ w`

We prove that `Nat.primeCounting ⌊w⌋₊ · log ⌈w⌉₊` is eventually bounded by a
constant multiple of `w`.  This is the classical Chebyshev estimate
`π(x) ≪ x / log x` (Mathlib's `Chebyshev.eventually_primeCounting_le`),
multiplied by `log ⌈w⌉ ≍ log w`.

The only extra observation needed is `log ⌈w⌉₊ ≤ 2 log w` for `w ≥ 2`, which
follows from `⌈w⌉ ≤ w + 1 ≤ w²`.
-/

set_option autoImplicit false

namespace Work.HP

open Filter

theorem pi_mul_log_eventually_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ w in Filter.atTop,
      (Nat.primeCounting ⌊w⌋₊ : ℝ) * Real.log ⌈w⌉₊ ≤ C * w := by
  refine ⟨10, by norm_num, ?_⟩
  -- Chebyshev's upper bound, specialised to `ε = 1`.
  have hcheb : ∀ᶠ w : ℝ in Filter.atTop,
      (Nat.primeCounting ⌊w⌋₊ : ℝ) ≤ 5 * w / Real.log w := by
    have h := Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with w hw hw1
    have hlog : 0 < Real.log w := Real.log_pos hw1
    have hlog4 : Real.log 4 + 1 ≤ 5 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
      linarith
    have : (Real.log 4 + 1) * w / Real.log w ≤ 5 * w / Real.log w := by
      rw [div_le_div_iff_of_pos_right hlog]
      exact mul_le_mul_of_nonneg_right hlog4 (le_of_lt (by linarith))
    linarith
  filter_upwards [hcheb, eventually_ge_atTop (2 : ℝ)] with w hw hw2
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  -- `log ⌈w⌉₊ ≤ 2 log w`, since `⌈w⌉ ≤ w + 1 ≤ w²` for `w ≥ 2`.
  have hlogM : Real.log ⌈w⌉₊ ≤ 2 * Real.log w := by
    have hceil : (⌈w⌉₊ : ℝ) ≤ w ^ 2 := by
      have h1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ w by linarith)
      nlinarith [hw2, sq_nonneg (w - 1)]
    have hpos : 0 < (⌈w⌉₊ : ℝ) := by
      have h1 : (1 : ℝ) ≤ (⌈w⌉₊ : ℝ) := le_trans (by linarith) (Nat.le_ceil w)
      linarith
    calc Real.log ⌈w⌉₊ ≤ Real.log (w ^ 2) := Real.log_le_log hpos hceil
      _ = 2 * Real.log w := by rw [Real.log_pow]; norm_num
  have hlogMnn : 0 ≤ Real.log ⌈w⌉₊ := by
    apply Real.log_nonneg
    exact le_trans (by linarith) (Nat.le_ceil w)
  calc (Nat.primeCounting ⌊w⌋₊ : ℝ) * Real.log ⌈w⌉₊
      ≤ (5 * w / Real.log w) * Real.log ⌈w⌉₊ := mul_le_mul_of_nonneg_right hw hlogMnn
    _ ≤ (5 * w / Real.log w) * (2 * Real.log w) :=
        mul_le_mul_of_nonneg_left hlogM (div_nonneg (by linarith) (le_of_lt hlogw))
    _ = 10 * w := by
        field_simp
        ring

end Work.HP
