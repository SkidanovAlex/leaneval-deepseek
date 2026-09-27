import Mathlib
import Submission.Work.Mostow.localIsomDefs

open Filter Asymptotics
open scoped Topology

namespace Work.Mostow

theorem diniResidual {n : ℕ} (γ : ℝ → Submission.Mostow.E n) (t : ℝ)
    (v : Submission.Mostow.E n) (hv : HasDerivAt γ v t) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ h ∈ Set.Ioo 0 δ, ‖γ (t + h) - γ t - h • v‖ ≤ η * h := by
  have hf : ∀ᶠ x in 𝓝 t, ‖γ x - γ t - (x - t) • v‖ ≤ η * ‖x - t‖ := by
    have h := hv.isLittleO.def hη
    simpa only [ContinuousLinearMap.toSpanSingleton_apply] using h
  have ht : Tendsto (fun h : ℝ => t + h) (𝓝[>] (0:ℝ)) (𝓝 t) := by
    have h0 := (show Tendsto (fun _ : ℝ => t) (𝓝[>] (0:ℝ)) (𝓝 t) from tendsto_const_nhds).add
      (tendsto_id.mono_right (nhdsWithin_le_nhds : (𝓝[>] (0:ℝ)) ≤ 𝓝 0))
    simpa using h0
  have hff : ∀ᶠ h in 𝓝[>] (0:ℝ), ‖γ (t + h) - γ t - h • v‖ ≤ η * h := by
    filter_upwards [ht.eventually hf, self_mem_nhdsWithin] with h hb hpos
    rw [Set.mem_Ioi] at hpos
    simpa only [add_sub_cancel_left, Real.norm_of_nonneg hpos.le] using hb
  rw [eventually_nhdsWithin_iff] at hff
  rw [Metric.eventually_nhds_iff] at hff
  obtain ⟨ε, hε, hsub⟩ := hff
  exact ⟨ε, hε, fun h hh =>
    hsub (by rw [Real.dist_eq, sub_zero, abs_of_pos hh.1]; exact hh.2) hh.1⟩

end Work.Mostow
