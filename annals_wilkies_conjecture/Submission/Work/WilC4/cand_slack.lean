import Mathlib
import Submission.Work.WilC4.rpow_one_add_le_two
import Submission.Work.WilC4.half_le_rpow_one_sub
import Submission.Work.WilC4.logb_div_tendsto_zero

open Filter

namespace Work.WilC4

theorem cand_slack (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ β : ℝ, R ≤ β →
      1 ≤ β ∧ (1 + 1 / (β * ρ)) ^ (Real.logb 2 β) ≤ 2 ∧
      (1 - 1 / (β * ρ)) ^ (Real.logb 2 β) ≥ 1 / 2 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Eventual non-triviality of the two bases.
  have h1 : ∀ᶠ β : ℝ in atTop, (1:ℝ) ≤ β := Filter.eventually_ge_atTop 1
  have h2 : ∀ᶠ β : ℝ in atTop, 1 / (β * ρ) ≤ 1 / 2 := by
    filter_upwards [Filter.eventually_ge_atTop (2 / ρ)] with β hβ
    have hβρ : 2 ≤ β * ρ := by
      have h := mul_le_mul_of_nonneg_right hβ hρ.le
      rwa [div_mul_cancel₀ (2:ℝ) hρ.ne'] at h
    have hβρpos : 0 < β * ρ := lt_of_lt_of_le (by norm_num) hβρ
    rw [div_le_iff₀ hβρpos]
    linarith
  -- The exponent times the base-displacement stays bounded by `log 2 / 2`.
  have h3 : ∀ᶠ β : ℝ in atTop, Real.logb 2 β / (β * ρ) ≤ Real.log 2 / 2 :=
    (logb_div_tendsto_zero ρ hρ).eventually_le_const (by linarith)
  have hall : ∀ᶠ β : ℝ in atTop,
      1 ≤ β ∧ 1 / (β * ρ) ≤ 1 / 2 ∧ Real.logb 2 β / (β * ρ) ≤ Real.log 2 / 2 :=
    h1.and (h2.and h3)
  obtain ⟨R0, hR0⟩ := Filter.eventually_atTop.1 hall
  refine ⟨max R0 1, le_max_right _ _, ?_⟩
  intro β hβ
  have hR0β : R0 ≤ β := le_trans (le_max_left _ _) hβ
  have hβ1 : (1:ℝ) ≤ β := le_trans (le_max_right _ _) hβ
  obtain ⟨hb1, hb2, hb3⟩ := hR0 β hR0β
  have hβρpos : 0 < β * ρ := mul_pos (lt_of_lt_of_le one_pos hβ1) hρ
  have hu0 : 0 ≤ 1 / (β * ρ) := div_nonneg zero_le_one hβρpos.le
  have hu1 : 1 / (β * ρ) ≤ 1 / 2 := hb2
  have hn : 0 ≤ Real.logb 2 β := by
    rw [Real.logb]
    exact div_nonneg (Real.log_nonneg hβ1) hlog2pos.le
  have hnu : Real.logb 2 β * (1 / (β * ρ)) ≤ Real.log 2 / 2 := by
    rw [mul_one_div]; exact hb3
  exact ⟨hb1, rpow_one_add_le_two _ _ hu0 hn hnu,
    half_le_rpow_one_sub _ _ hu0 hu1 hn hnu⟩

end Work.WilC4
