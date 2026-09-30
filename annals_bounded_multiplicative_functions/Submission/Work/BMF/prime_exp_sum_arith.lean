import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Filter Real
open scoped Topology

/-- **Elementary asymptotic facts** used to absorb error terms.
For every `c > 0` there is `P₀ ≥ 2` such that for all real `P ≥ P₀`:
* `log P · exp(-c·(log P)^{1/10}) ≤ 1`  (a fixed power of `log` is swallowed by `exp(-c log^{1/10})`),
* `√P · (log P)^3 ≤ P`  (polynomial growth beats powers of `log`),
* `1 ≤ P / (log P)^2` and `4 ≤ P`,
* `log (2P) ≤ 2 log P`. -/
theorem prime_exp_sum_arith (c : ℝ) (hc : 0 < c) :
    ∃ P₀ : ℝ, 2 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      Real.log P * Real.exp (-c * Real.log P ^ (1 / 10 : ℝ)) ≤ 1 ∧
      Real.sqrt P * (Real.log P) ^ 3 ≤ P ∧
      1 ≤ P / (Real.log P) ^ 2 ∧
      Real.log (2 * P) ≤ 2 * Real.log P ∧
      4 ≤ P := by
  -- (1) `log P * exp (-c * (log P)^(1/10)) → 0`
  have h1 : ∀ᶠ P : ℝ in atTop,
      Real.log P * Real.exp (-c * Real.log P ^ (1 / 10 : ℝ)) ≤ 1 := by
    have hbase : Tendsto (fun P : ℝ => (Real.log P) ^ (1 / 10 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp Real.tendsto_log_atTop
    have hcomp : Tendsto
        (fun P : ℝ => ((Real.log P) ^ (1 / 10 : ℝ)) ^ (10 : ℝ) *
          Real.exp (-c * ((Real.log P) ^ (1 / 10 : ℝ)))) atTop (𝓝 0) :=
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 10 c hc).comp hbase
    have hEq : (fun P : ℝ => ((Real.log P) ^ (1 / 10 : ℝ)) ^ (10 : ℝ) *
          Real.exp (-c * ((Real.log P) ^ (1 / 10 : ℝ))))
        =ᶠ[atTop] (fun P : ℝ => Real.log P * Real.exp (-c * Real.log P ^ (1 / 10 : ℝ))) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with P hP
      have hlog : 0 ≤ Real.log P := Real.log_nonneg hP
      have hpow : ((Real.log P) ^ (1 / 10 : ℝ)) ^ (10 : ℝ) = Real.log P := by
        rw [← Real.rpow_mul hlog (1 / 10) 10, show (1 / 10 : ℝ) * 10 = 1 by norm_num,
          Real.rpow_one]
      simp only [hpow]
    have hlim : Tendsto (fun P : ℝ => Real.log P * Real.exp (-c * Real.log P ^ (1 / 10 : ℝ)))
        atTop (𝓝 0) := Tendsto.congr' hEq hcomp
    exact (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun P hP => le_of_lt hP)
  -- (2) `√P * (log P)^3 ≤ P`
  have h2 : ∀ᶠ P : ℝ in atTop, Real.sqrt P * (Real.log P) ^ 3 ≤ P := by
    have hlittle : (fun P : ℝ => Real.log P ^ 3) =o[atTop] (fun P : ℝ => P ^ (1 / 2 : ℝ)) := by
      simpa [Real.rpow_natCast] using
        isLittleO_log_rpow_rpow_atTop 3 (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [hlittle.eventuallyLE, eventually_gt_atTop (1 : ℝ)] with P hP hP1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.log_nonneg hP1.le) 3),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) (1 / 2 : ℝ))] at hP
    have hP' : (Real.log P) ^ 3 ≤ Real.sqrt P := by
      rw [Real.sqrt_eq_rpow]; exact hP
    calc Real.sqrt P * (Real.log P) ^ 3 ≤ Real.sqrt P * Real.sqrt P :=
          mul_le_mul_of_nonneg_left hP' (Real.sqrt_nonneg P)
      _ = P := Real.mul_self_sqrt (by linarith)
  -- (3) `1 ≤ P / (log P)^2`
  have h3 : ∀ᶠ P : ℝ in atTop, 1 ≤ P / (Real.log P) ^ 2 := by
    have hlittle : (fun P : ℝ => Real.log P ^ 2) =o[atTop] (fun P : ℝ => P) := by
      simpa [Real.rpow_one, Real.rpow_natCast] using
        isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hlittle.eventuallyLE, eventually_gt_atTop (1 : ℝ)] with P hP hP1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.log_nonneg hP1.le) 2),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ P)] at hP
    have hpos : 0 < (Real.log P) ^ 2 := pow_pos (Real.log_pos hP1) 2
    rw [one_le_div hpos]
    exact hP
  -- (4) `log (2P) ≤ 2 log P`
  have h4 : ∀ᶠ P : ℝ in atTop, Real.log (2 * P) ≤ 2 * Real.log P := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with P hP
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : P ≠ 0)]
    have h2log : Real.log 2 ≤ Real.log P := Real.log_le_log (by norm_num) hP
    linarith
  have hall : ∀ᶠ P : ℝ in atTop,
      Real.log P * Real.exp (-c * Real.log P ^ (1 / 10 : ℝ)) ≤ 1 ∧
      Real.sqrt P * (Real.log P) ^ 3 ≤ P ∧
      1 ≤ P / (Real.log P) ^ 2 ∧
      Real.log (2 * P) ≤ 2 * Real.log P ∧
      4 ≤ P := by
    filter_upwards [h1, h2, h3, h4, eventually_ge_atTop (4 : ℝ)] with P h1P h2P h3P h4P h5P
    exact ⟨h1P, h2P, h3P, h4P, h5P⟩
  obtain ⟨a, ha⟩ := eventually_atTop.1 hall
  refine ⟨max a 4, ?_, ?_⟩
  · have : (4 : ℝ) ≤ max a 4 := le_max_right a 4
    linarith
  · intro P hP
    exact ha P (le_trans (le_max_left a 4) hP)

end Work.BMF
