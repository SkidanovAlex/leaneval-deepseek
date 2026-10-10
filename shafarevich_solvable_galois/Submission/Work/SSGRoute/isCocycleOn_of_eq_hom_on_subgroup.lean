import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- If `f` agrees on a subgroup `H ≤ Γ` with an additive shadow of a multiplicative homomorphism
`f0 : H →* M`, and `act` kills `H`, then `f` is a `1`-cocycle on `H` for the action through
`act` (which is trivial there). -/
theorem isCocycleOn_of_eq_hom_on_subgroup {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (act : Γ →* G) (H : Subgroup Γ) (hact : H ≤ act.ker)
    (f0 : ↥H →* Multiplicative M) (f : Γ → M)
    (hf : ∀ (σ : Γ) (hσ : σ ∈ H), f σ = (f0 ⟨σ, hσ⟩).toAdd) :
    SSGRoute.IsCocycleOn act H f := by
  intro g hg h hh
  have hg1 : act g = 1 := by
    have : g ∈ act.ker := hact hg
    simpa [MonoidHom.mem_ker] using this
  have key : f0 ⟨g * h, H.mul_mem hg hh⟩ = f0 ⟨g, hg⟩ * f0 ⟨h, hh⟩ := by
    rw [← map_mul]
    rfl
  rw [hf g hg, hf h hh, hf (g * h) (H.mul_mem hg hh), hg1, one_smul, key]
  rfl

end Work.SSGRoute
