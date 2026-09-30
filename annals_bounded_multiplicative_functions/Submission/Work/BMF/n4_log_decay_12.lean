import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem n4_log_decay_12 (c : ℝ) (hc : 0 < c) (A : ℕ) :
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      (Real.log P) ^ A * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ)) ≤ 1 := by
  have hmain : Filter.Tendsto (fun x : ℝ => x ^ A * Real.exp (-c * x ^ (1 / 12 : ℝ)))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun t : ℝ => t ^ ((12 * A : ℕ) : ℝ) * Real.exp (-c * t))
        Filter.atTop (nhds 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((12 * A : ℕ) : ℝ) c hc
    have h1 : Filter.Tendsto (fun x : ℝ => x ^ (1 / 12 : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_rpow_atTop (by norm_num)
    refine (h0.comp h1).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_apply]
    have hpow : (x ^ (1 / 12 : ℝ)) ^ ((12 * A : ℕ) : ℝ) = x ^ A := by
      rw [← Real.rpow_mul hx]
      have hs : (1 / 12 : ℝ) * ((12 * A : ℕ) : ℝ) = (A : ℝ) := by push_cast; ring
      rw [hs, Real.rpow_natCast]
    rw [hpow]
  have hcomp : Filter.Tendsto
      (fun P : ℝ => (Real.log P) ^ A * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ)))
      Filter.atTop (nhds 0) := hmain.comp Real.tendsto_log_atTop
  have hev : ∀ᶠ P in Filter.atTop,
      (Real.log P) ^ A * Real.exp (-c * Real.log P ^ (1 / 12 : ℝ)) < 1 :=
    (tendsto_order.1 hcomp).2 1 (by norm_num)
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.1 hev
  exact ⟨max P₀ 1, le_max_right _ _, fun P hP => le_of_lt (hP₀ P (le_trans (le_max_left _ _) hP))⟩

end Work.BMF
