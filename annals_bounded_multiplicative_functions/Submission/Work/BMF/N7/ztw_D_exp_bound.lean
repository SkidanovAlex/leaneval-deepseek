import Mathlib
import Submission.Work.BMF.ztw_asym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N7

open Filter
open scoped Topology

/-- `log` dies against every positive power: for `ε > 0` and `r > 0`, eventually
`log L ≤ ε * L ^ r`. -/
private lemma ev_log_le_mul_rpow (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) :
    ∀ᶠ L : ℝ in atTop, Real.log L ≤ ε * L ^ r := by
  filter_upwards [(isLittleO_log_rpow_atTop hr).bound hε, eventually_ge_atTop (1 : ℝ)]
    with L hL hL1
  rw [Real.norm_of_nonneg (Real.log_nonneg hL1),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ L) r)] at hL
  exact hL

/-- `(2 L^{21/20})^{6/7} (log 3 + log (2 L^{21/20})) ≤ 2 L^{11/12}` eventually: after `mul_rpow`/`rpow_mul`/`log_mul`/`log_rpow` this is `2^{6/7} L^{9/10} (log 3 + log 2 + (21/20) log L) ≤ 2 L^{11/12}`, and `log L` dies against `L^{1/60}`. -/
theorem ztw_D_exp_bound : ∀ᶠ L : ℝ in Filter.atTop, (2 * L ^ (21 / 20 : ℝ)) ^ (6 / 7 : ℝ) * (Real.log 3 + Real.log (2 * L ^ (21 / 20 : ℝ))) ≤ 2 * L ^ (11 / 12 : ℝ) := by
  -- `log L ≤ (10/21) L^{1/60}` eventually.
  have hlogL : ∀ᶠ L : ℝ in atTop, Real.log L ≤ (10 / 21 : ℝ) * L ^ (1 / 60 : ℝ) :=
    ev_log_le_mul_rpow (10 / 21) (1 / 60) (by norm_num) (by norm_num)
  -- `log 3 + log 2 ≤ (1/2) L^{1/60}` eventually.
  have hconst : ∀ᶠ L : ℝ in atTop, Real.log 3 + Real.log 2 ≤ (1 / 2 : ℝ) * L ^ (1 / 60 : ℝ) := by
    have h := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 60 by norm_num)).eventually_ge_atTop
      (2 * (Real.log 3 + Real.log 2))
    filter_upwards [h] with L hL
    linarith
  filter_upwards [hlogL, hconst, eventually_ge_atTop (1 : ℝ)] with L hlogL hconst hL1
  have hLpos : 0 < L := by linarith
  -- The two logarithms combine and are dominated by `L^{1/60}`.
  have hkeylog : Real.log 3 + (Real.log 2 + (21 / 20 : ℝ) * Real.log L) ≤ L ^ (1 / 60 : ℝ) := by
    have hmul : (21 / 20 : ℝ) * Real.log L ≤ (1 / 2 : ℝ) * L ^ (1 / 60 : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hlogL (by norm_num : (0 : ℝ) ≤ (21 / 20))
      have he : (21 / 20 : ℝ) * ((10 / 21 : ℝ) * L ^ (1 / 60 : ℝ)) =
          (1 / 2 : ℝ) * L ^ (1 / 60 : ℝ) := by ring
      rw [he] at h1
      exact h1
    linarith
  -- Rewrite the power.
  have hpow : (2 * L ^ (21 / 20 : ℝ)) ^ (6 / 7 : ℝ) = 2 ^ (6 / 7 : ℝ) * L ^ (9 / 10 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hLpos.le _),
        ← Real.rpow_mul hLpos.le]
    norm_num
  -- Rewrite the logarithm.
  have hlog2 : Real.log (2 * L ^ (21 / 20 : ℝ)) = Real.log 2 + (21 / 20 : ℝ) * Real.log L := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hLpos _)), Real.log_rpow hLpos]
  have hp : (2 * L ^ (21 / 20 : ℝ)) ^ (6 / 7 : ℝ) ≤ 2 * L ^ (9 / 10 : ℝ) := by
    rw [hpow]
    have h2 : (2 : ℝ) ^ (6 / 7 : ℝ) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)
        (show (6 / 7 : ℝ) ≤ (1 : ℝ) by norm_num)
      rw [Real.rpow_one] at h
      exact h
    exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hLpos.le _)
  have hq : Real.log 3 + Real.log (2 * L ^ (21 / 20 : ℝ)) ≤ L ^ (1 / 60 : ℝ) := by
    rw [hlog2]; exact hkeylog
  have hqnonneg : 0 ≤ Real.log 3 + Real.log (2 * L ^ (21 / 20 : ℝ)) := by
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have h2L : 1 ≤ 2 * L ^ (21 / 20 : ℝ) := by
      have h1 : 1 ≤ L ^ (21 / 20 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
      linarith
    have h0 : 0 ≤ Real.log (2 * L ^ (21 / 20 : ℝ)) := Real.log_nonneg h2L
    linarith
  calc (2 * L ^ (21 / 20 : ℝ)) ^ (6 / 7 : ℝ) *
          (Real.log 3 + Real.log (2 * L ^ (21 / 20 : ℝ)))
      ≤ (2 * L ^ (9 / 10 : ℝ)) * L ^ (1 / 60 : ℝ) :=
        mul_le_mul hp hq hqnonneg (by have := Real.rpow_nonneg hLpos.le (9 / 10 : ℝ); linarith)
    _ = 2 * L ^ (11 / 12 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hLpos]
        congr 1
        norm_num

end Work.BMF.N7
