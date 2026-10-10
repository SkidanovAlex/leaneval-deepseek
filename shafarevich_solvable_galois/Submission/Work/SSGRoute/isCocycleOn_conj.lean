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

theorem isCocycleOn_conj {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (ρ : Γ →* G) {H : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsCocycleOn ρ H f) (σ : Γ) (hσ : ∀ n ∈ H, σ⁻¹ * n * σ ∈ H) :
    SSGRoute.IsCocycleOn ρ H (fun n => ρ σ • f (σ⁻¹ * n * σ)) := by
  intro g hg h hh
  show ρ σ • f (σ⁻¹ * (g * h) * σ) = ρ σ • f (σ⁻¹ * g * σ) + ρ g • (ρ σ • f (σ⁻¹ * h * σ))
  have hg' : σ⁻¹ * g * σ ∈ H := hσ g hg
  have hh' : σ⁻¹ * h * σ ∈ H := hσ h hh
  have hgh : σ⁻¹ * (g * h) * σ = (σ⁻¹ * g * σ) * (σ⁻¹ * h * σ) := by group
  rw [hgh, hf _ hg' _ hh', smul_add]
  congr 1
  rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul]
  congr 1
  group

end Work.SSGRoute
