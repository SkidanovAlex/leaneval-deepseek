import Mathlib
import Submission.Work.BW.finrank_lieSubDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem map_lieCons_ker_eq {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) :
    (LinearMap.ker (mLie M)).map (lieCons N) =
      LinearMap.ker (lieProj0 N) ⊓ LinearMap.ker ((mLie M).comp (lieTail N)) := by
  ext v
  constructor
  · intro hv
    rw [Submodule.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker]
      simp [lieProj0, lieCons]
    · rw [LinearMap.mem_ker, LinearMap.comp_apply, lieTail_lieCons]
      exact LinearMap.mem_ker.mp hu
  · intro hv
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hv
    obtain ⟨hv0, hv1⟩ := hv
    rw [Submodule.mem_map]
    refine ⟨lieTail N v, LinearMap.mem_ker.mpr hv1, ?_⟩
    exact lieCons_lieTail_of_apply_zero (by simpa [lieProj0] using hv0)

end Work.BW
