import Mathlib
import Submission.Work.HP.ceil_logb_bounds
import Submission.Work.HP.Q44Main.qsum_clog_logb

/-!
# `q44S_window_inputs`

Window bookkeeping for the dyadic decomposition of the range `(1, 8 Kmink (Δ+1)]`.

For `Kmink ≥ 1` we produce a single constant `Clog ≥ 1` such that for every real `Δ ≥ 1`,
writing `n = ⌈logb 2 (8 Kmink (Δ+1))⌉₊`,

* `2 ^ n ≤ 32 Kmink Δ` — the top dyadic window is comparable with `Δ`;
* `n + 1 ≤ Clog · log (2 Δ)` — the number of windows is `O(log Δ)`.

The first is the sharp dyadic bound `2 ^ ⌈logb 2 x⌉₊ ≤ 2 x` (`Work.HP.ceil_logb_bounds`)
applied to `x = 8 Kmink (Δ+1)` together with `Δ + 1 ≤ 2 Δ`.  The second is
`Work.HP.Q44Main.qsum_clog_logb`, whose constant we simply enlarge to be `≥ 1`.
-/

namespace Work.HP.Q44Main

theorem q44S_window_inputs (Kmink : ℝ) (hKmink : 1 ≤ Kmink) :
    ∃ Clog : ℝ, 0 < Clog ∧ 1 ≤ Clog ∧ ∀ Δ : ℝ, 1 ≤ Δ →
      (2 : ℝ) ^ (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊) ≤ 32 * Kmink * Δ
      ∧ ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℕ) : ℝ) + 1 ≤ Clog * Real.log (2 * Δ) := by
  obtain ⟨C, _hCpos, hCall⟩ := qsum_clog_logb Kmink hKmink
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left 1 C), le_max_left 1 C, ?_⟩
  intro Δ hΔ
  have hKpos : 0 < Kmink := lt_of_lt_of_le zero_lt_one hKmink
  refine ⟨?_, ?_⟩
  · -- top window `2 ^ n` is at most `32 Kmink Δ`
    have hx1 : (1 : ℝ) ≤ 8 * Kmink * (Δ + 1) := by nlinarith [hKmink, hΔ]
    have hb : (2 : ℝ) ^ (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℕ)
        ≤ 2 * (8 * Kmink * (Δ + 1)) := (Work.HP.ceil_logb_bounds hx1).2
    have hΔ1 : Δ + 1 ≤ 2 * Δ := by linarith
    nlinarith [hb, hΔ1, hKpos]
  · -- number of windows is `O(log Δ)`
    have hlog : 0 < Real.log (2 * Δ) := Real.log_pos (by linarith)
    calc ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℕ) : ℝ) + 1
        ≤ C * Real.log (2 * Δ) := hCall Δ hΔ
      _ ≤ max 1 C * Real.log (2 * Δ) :=
          mul_le_mul_of_nonneg_right (le_max_right 1 C) hlog.le

end Work.HP.Q44Main
