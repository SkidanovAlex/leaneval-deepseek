import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.AbsoluteKummer.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- `IsLocConst2` — right invariance of a two-variable function under an open subgroup,
componentwise — implies local constancy of the corresponding function on the product `Γ × Γ`
(whose topology is the product topology). -/
theorem bridge_isLocConst2_isLocallyConstant {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group G] [AddCommGroup M] [DistribMulAction G M] (c : Γ × Γ → M) (hc : SSGRoute.IsLocConst2 (fun g h => c (g, h))) : Work.AbsoluteKummer.IsLocallyConstant c := by
  obtain ⟨U, hUopen, hUinv⟩ := hc
  intro x
  obtain ⟨g₀, h₀⟩ := x
  -- `g₀ * U × h₀ * U` is an open neighbourhood of `x` on which `c` is constant.
  refine ⟨{p : Γ × Γ | g₀⁻¹ * p.1 ∈ U ∧ h₀⁻¹ * p.2 ∈ U}, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun p : Γ × Γ => (g₀⁻¹ * p.1, h₀⁻¹ * p.2)) := by continuity
    have hset : {p : Γ × Γ | g₀⁻¹ * p.1 ∈ U ∧ h₀⁻¹ * p.2 ∈ U}
        = (fun p : Γ × Γ => (g₀⁻¹ * p.1, h₀⁻¹ * p.2)) ⁻¹' ((U : Set Γ) ×ˢ (U : Set Γ)) := by
      ext p; simp [Set.mem_prod]
    rw [hset]
    exact (hUopen.prod hUopen).preimage hcont
  · exact ⟨by rw [inv_mul_cancel]; exact U.one_mem, by rw [inv_mul_cancel]; exact U.one_mem⟩
  · intro p hp
    have hp1 : p.1 = g₀ * (g₀⁻¹ * p.1) := (mul_inv_cancel_left g₀ p.1).symm
    have hp2 : p.2 = h₀ * (h₀⁻¹ * p.2) := (mul_inv_cancel_left h₀ p.2).symm
    have hthis := hUinv g₀ h₀ (g₀⁻¹ * p.1) (h₀⁻¹ * p.2) hp.1 hp.2
    rw [show p = (g₀ * (g₀⁻¹ * p.1), h₀ * (h₀⁻¹ * p.2)) from Prod.ext hp1 hp2]
    exact hthis

end Work.SSGRoute
