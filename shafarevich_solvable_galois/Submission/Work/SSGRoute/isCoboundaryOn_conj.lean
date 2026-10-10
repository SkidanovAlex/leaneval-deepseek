import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Coboundaries on a subgroup are stable under conjugation of the argument: if
`f n = ρ n • m - m` on `H` and `σ⁻¹ H σ ⊆ H`, then the conjugated function
`n ↦ ρ σ • f (σ⁻¹ * n * σ)` is the coboundary of `ρ σ • m` on `H`. -/
theorem isCoboundaryOn_conj {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (ρ : Γ →* G) {H : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsCoboundaryOn ρ H f) (σ : Γ) (hσ : ∀ n ∈ H, σ⁻¹ * n * σ ∈ H) :
    SSGRoute.IsCoboundaryOn ρ H (fun n => ρ σ • f (σ⁻¹ * n * σ)) := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨ρ σ • m, ?_⟩
  intro g hg
  have hg' : σ⁻¹ * g * σ ∈ H := hσ g hg
  change ρ σ • f (σ⁻¹ * g * σ) = ρ g • (ρ σ • m) - ρ σ • m
  rw [hm _ hg', smul_sub]
  have h1 : ρ σ • (ρ (σ⁻¹ * g * σ) • m) = ρ (g * σ) • m := by
    rw [← mul_smul, ← map_mul]
    congr 1
    group
  have h2 : ρ g • (ρ σ • m) = ρ (g * σ) • m := by
    rw [← mul_smul, ← map_mul]
  rw [h1, h2]

end Work.SSGRoute
