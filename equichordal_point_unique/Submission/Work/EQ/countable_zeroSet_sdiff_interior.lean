import Mathlib

open Set Filter Topology

namespace Work.EQ

/-- **The isolated zeros of an analytic function are countable.**  For open `U ⊆ ℂ` and
`r : ℂ → ℂ` analytic on `U`, the points of `U` where `r` vanishes but not identically on a
neighbourhood form a countable set.
Route: at such a point `w`, `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` gives
`∀ᶠ z in 𝓝[≠] w, r z ≠ 0`, so the set is discrete; each of its points has a distinct rational ball
meeting it only there, so it injects into the countable set of rational balls. -/
theorem countable_zeroSet_sdiff_interior {U : Set ℂ} {r : ℂ → ℂ} (hU : IsOpen U)
    (hr : AnalyticOnNhd ℂ r U) :
    ({w ∈ U | r w = 0} \ interior {w ∈ U | r w = 0}).Countable := by
  set S : Set ℂ := {w ∈ U | r w = 0} \ interior {w ∈ U | r w = 0} with hS
  have hdisc : IsDiscrete S := by
    rw [isDiscrete_iff_nhdsNE]
    intro w hw
    rw [hS, Set.mem_sdiff, Set.mem_ofPred_eq] at hw
    obtain ⟨hwZ, hwint⟩ := hw
    obtain ⟨hwU, _⟩ := hwZ
    rcases (hr w hwU).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      apply hwint
      rw [mem_interior_iff_mem_nhds]
      exact Filter.inter_mem (hU.mem_nhds hwU) h
    · rw [← le_bot_iff]
      have hmem : Sᶜ ∈ 𝓝[≠] w := by
        refine Filter.mem_of_superset h ?_
        intro z hz
        simp only [Set.mem_ofPred_eq] at hz
        simp only [Set.mem_compl_iff]
        intro hzS
        rw [hS, Set.mem_sdiff, Set.mem_ofPred_eq] at hzS
        exact hz hzS.1.2
      calc 𝓝[≠] w ⊓ 𝓟 S ≤ 𝓟 Sᶜ ⊓ 𝓟 S := inf_le_inf_right _ (Filter.le_principal_iff.mpr hmem)
        _ = ⊥ := by simp
  exact (HereditarilyLindelofSpace.isLindelof S).countable_of_isDiscrete hdisc

end Work.EQ
