import Mathlib

namespace Work.LinnikAreas.Density4

open Filter Asymptotics
open scoped Topology

/-- The iterated logarithm grows slower than the identity: `log (log x) = o(x)` at `atTop`. -/
private lemma isLittleO_log_log_id :
    (fun x : ℝ => Real.log (Real.log x)) =o[atTop] (id : ℝ → ℝ) := by
  have h1 : (fun x : ℝ => Real.log (Real.log x)) =o[atTop] (fun x : ℝ => Real.log x) :=
    Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  exact h1.trans Real.isLittleO_log_id_atTop

/-- `log (log (log q)) / log q → 0` along the naturals. -/
private lemma tendsto_lll_div :
    Tendsto (fun q : ℕ => Real.log (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
      atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log (Real.log x) / x) atTop (𝓝 0) :=
    isLittleO_log_log_id.tendsto_div_nhds_zero
  exact h.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- `1 / log q → 0` along the naturals, since `log q → ∞`. -/
private lemma tendsto_one_div_log :
    Tendsto (fun q : ℕ => 1 / Real.log (q : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact (h.inv_tendsto_atTop).congr (fun q => (one_div _).symm)

theorem lamMax_div_log_small (c : ℝ) (hc : 0 < c) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (Real.log (Real.log (Real.log (q : ℝ))) / 3 + 1) / Real.log (q : ℝ) < c := by
  have hpos : ∀ᶠ q : ℕ in atTop, (0 : ℝ) < Real.log (q : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0
  -- The full expression is eventually equal to the sum of the two pieces above.
  have hH : Tendsto
      (fun q : ℕ => (Real.log (Real.log (Real.log (q : ℝ))) / 3 + 1) / Real.log (q : ℝ))
      atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun q : ℕ =>
          Real.log (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) / 3
            + 1 / Real.log (q : ℝ))
        atTop (𝓝 ((0 : ℝ) / 3 + 0)) :=
      (tendsto_lll_div.div_const 3).add tendsto_one_div_log
    have hsum0 : Tendsto
        (fun q : ℕ =>
          Real.log (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) / 3
            + 1 / Real.log (q : ℝ))
        atTop (𝓝 0) := by
      simpa using hsum
    refine hsum0.congr' ?_
    filter_upwards [hpos] with q hq
    field_simp
  exact Filter.eventually_atTop.1 ((tendsto_order.1 hH).2 c hc)

end Work.LinnikAreas.Density4
