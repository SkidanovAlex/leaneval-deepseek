import Mathlib
import Submission.Work.LinnikContract.Defs

namespace Work.LinnikAreas.Density4

open Filter Asymptotics Topology

/-- The iterated logarithm grows slower than the identity: `log (log x) = o(x)` at `atTop`. -/
private lemma isLittleO_log_log_id :
    (fun x : ℝ => Real.log (Real.log x)) =o[atTop] (id : ℝ → ℝ) := by
  have h1 : (fun x : ℝ => Real.log (Real.log x)) =o[atTop] (fun x : ℝ => Real.log x) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  exact h1.trans Real.isLittleO_log_id_atTop

/-- `log (log x) / x → 0` as `x → ∞`. -/
private lemma tendsto_log_log_div :
    Tendsto (fun x : ℝ => Real.log (Real.log x) / x) atTop (𝓝 (0 : ℝ)) := by
  simpa using isLittleO_log_log_id.tendsto_div_nhds_zero

theorem exists_log_threshold {A δ : ℝ} (hδ : 0 < δ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      1 < Real.log (q : ℝ) ∧
      |A| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) ∧
      Work.LinnikContract.lamMax q / Real.log (q : ℝ) ≤ δ := by
  have h1 : ∀ᶠ q : ℕ in atTop, 1 < Real.log (q : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 1
  have h2 : ∀ᶠ q : ℕ in atTop, |A| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    have hS : Tendsto (fun x : ℝ => Real.sqrt (Real.log (Real.log x))) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
    exact (hS.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop |A|
  have h3 : ∀ᶠ q : ℕ in atTop, Work.LinnikContract.lamMax q / Real.log (q : ℝ) ≤ δ := by
    have hE : Tendsto (fun q : ℕ => Real.log (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        atTop (𝓝 (0 : ℝ)) :=
      tendsto_log_log_div.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have h2' : Tendsto
        (fun q : ℕ => Real.log (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) / 3)
        atTop (𝓝 ((0 : ℝ) / 3)) :=
      hE.div_const 3
    have hlim : Tendsto
        (fun q : ℕ => Real.log (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) / 3)
        atTop (𝓝 (0 : ℝ)) := by
      simpa using h2'
    have key := (tendsto_order.1 hlim).2 δ hδ
    filter_upwards [key] with q hq
    rw [show Work.LinnikContract.lamMax q / Real.log (q : ℝ)
          = Real.log (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) / 3 by
        unfold Work.LinnikContract.lamMax; ring]
    exact le_of_lt hq
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨q₀, fun q hq => ?_⟩
  obtain ⟨ha, hb, hc⟩ := hq₀ q hq
  exact ⟨ha, hb, hc⟩

end Work.LinnikAreas.Density4
