import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology
set_option linter.unusedVariables false

namespace Commons.Analysis.Asymptotics

/-- Linear (and constant) growth is eventually dominated by any positive exponential
function of the form `2 ^ (c * l)` with `c > 0`. -/
theorem linear_le_mul_two_rpow (c : ℝ) (hc : 0 < c) (A K : ℝ) (hA : 0 ≤ A) (hK : 0 < K) :
    ∃ L : ℕ, ∀ l : ℕ, L ≤ l → A + (l : ℝ) ≤ K * (2 : ℝ) ^ (c * (l : ℝ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < c * Real.log 2 := mul_pos hc hlog2
  -- `l = o(2 ^ (c * l))` as `l → ∞`.
  have hlittle : (fun l : ℕ => (l : ℝ)) =o[atTop]
      (fun l : ℕ => (2 : ℝ) ^ (c * (l : ℝ))) := by
    have h := (isLittleO_rpow_exp_pos_mul_atTop (1 : ℝ) hb).natCast_atTop
    refine h.congr' ?_ ?_
    · filter_upwards with n
      rw [Real.rpow_one]
    · filter_upwards with n
      rw [show (c * Real.log 2) * (n : ℝ) = Real.log 2 * (c * (n : ℝ)) by ring]
      rw [← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  -- `2 ^ (c * l) → ∞`.
  have h2c : 1 < (2 : ℝ) ^ c := Real.one_lt_rpow (by norm_num) hc
  have hpow : Tendsto (fun l : ℕ => (2 : ℝ) ^ (c * (l : ℝ))) atTop atTop := by
    have h := tendsto_pow_atTop_atTop_of_one_lt h2c
    refine h.congr' (Eventually.of_forall fun l => ?_)
    rw [← Real.rpow_natCast ((2 : ℝ) ^ c) l]
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num) c (l : ℝ)]
  have hAdiv : Tendsto (fun l : ℕ => A / (2 : ℝ) ^ (c * (l : ℝ))) atTop (𝓝 0) :=
    hpow.const_div_atTop A
  have hldiv : Tendsto (fun l : ℕ => (l : ℝ) / (2 : ℝ) ^ (c * (l : ℝ))) atTop (𝓝 0) :=
    hlittle.tendsto_div_nhds_zero
  have hsum : Tendsto (fun l : ℕ => (A + (l : ℝ)) / (2 : ℝ) ^ (c * (l : ℝ))) atTop (𝓝 0) := by
    have := hAdiv.add hldiv
    simpa [add_div] using this
  have hev : ∀ᶠ l : ℕ in atTop, (A + (l : ℝ)) / (2 : ℝ) ^ (c * (l : ℝ)) < K :=
    hsum.eventually_lt_const hK
  have hev' : ∀ᶠ l : ℕ in atTop, A + (l : ℝ) ≤ K * (2 : ℝ) ^ (c * (l : ℝ)) := by
    filter_upwards [hev] with l hl
    have hpos : 0 < (2 : ℝ) ^ (c * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    rw [div_lt_iff₀ hpos] at hl
    linarith [hl, hA]
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.1 hev'
  exact ⟨L, hL⟩

end Commons.Analysis.Asymptotics