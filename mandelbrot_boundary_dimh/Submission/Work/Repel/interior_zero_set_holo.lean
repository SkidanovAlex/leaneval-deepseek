import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Repel

open scoped Topology

/-- Identity principle in its `interior` form: a holomorphic function on a preconnected open set
is not identically zero, hence the interior of its zero set is empty. -/
theorem interior_zero_set_holo {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : DifferentiableOn ℂ F U) (hne : ∃ u ∈ U, F u ≠ 0) :
    interior {u ∈ U | F u = 0} = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨z, hz⟩
  have hzU : z ∈ U := (interior_subset hz).1
  have hzS : ({u ∈ U | F u = 0} : Set ℂ) ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hz
  have hz0 : F =ᶠ[𝓝 z] 0 := Filter.mem_of_superset hzS fun y hy => hy.2
  obtain ⟨u0, hu0U, hu0ne⟩ := hne
  exact hu0ne
    ((hF.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hzU hz0 hu0U)

end Work.Repel
